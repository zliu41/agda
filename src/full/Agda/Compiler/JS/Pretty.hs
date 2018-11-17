{-# LANGUAGE OverloadedStrings #-}
module Agda.Compiler.JS.Pretty where

import Prelude hiding ( null )
import Data.List ( intercalate )
import Data.String ( IsString (fromString) )
import Data.Set ( Set, toList, singleton, insert, member )
import Data.Map ( Map, toAscList, empty, null )
import Text.Regex.TDFA (makeRegex, matchTest, Regex)

import Agda.Syntax.Common ( Nat )
import Agda.Utils.Hash

import Agda.Compiler.JS.Syntax hiding (exports)

-- Pretty-print a lambda-calculus expression as ECMAScript.

--- The indentation combinators of the pretty library does not fit C-like languages
--- like ECMAScript.
--- Here we implement a basic pretty printer with a better `indent`.
--- An alternative solution would be to depend on a pretty-printing library with
--- a similar `indent` operation.

data Doc
    = Doc String
    | Indent Int Doc
    | Beside Doc Doc
    | Above Doc Doc
    | Empty

render :: Doc -> String
render = go 0
  where
    go i Empty = ""
    go i (Doc s) = s
    go i (Beside d d') = go i d ++ go i d'
    go i (Above d d') = go i d ++ "\n" ++ replicate i ' ' ++ go i d'
    go i (Indent j d) = go (i+j) d

instance IsString Doc where
    fromString = Doc

instance Semigroup Doc where
    Empty <> d = d
    d <> Empty = d
    d <> d' = Beside d d'

instance Monoid Doc where
    mempty = Empty

infixl 5 $+$

($+$) :: Doc -> Doc -> Doc
Empty $+$ d = d
d $+$ Empty = d
d $+$ d' = Above d d'

text :: String -> Doc
text = Doc

indent :: Doc -> Doc
indent = Indent 2

punctuate :: Doc -> [Doc] -> [Doc]
punctuate _ []     = []
punctuate p (x:xs) = go x xs
                   where go y []     = [y]
                         go y (z:zs) = (y <> p) : go z zs

hcat :: [Doc] -> Doc
hcat = foldr (<>) mempty

hsep :: [Doc] -> Doc
hsep = hcat . punctuate " "

vcat :: [Doc] -> Doc
vcat = foldr ($+$) mempty

-- | Apply 'parens' to 'Doc' if boolean is true.
mparens :: Bool -> Doc -> Doc
mparens True  d = "(" <> d <> ")"
mparens False d = d


unescape :: Char -> String
unescape '"'      = "\\\""
unescape '\\'     = "\\\\"
unescape '\n'     = "\\n"
unescape '\r'     = "\\r"
unescape '\x2028' = "\\u2028"
unescape '\x2029' = "\\u2029"
unescape c        = [c]

unescapes :: String -> Doc
unescapes s = text $ concatMap unescape s

-- pretty n i e pretty-prints e, under n levels of de Bruijn binding

class Pretty a where
    pretty :: Nat -> a -> Doc

prettyShow :: Pretty a => a -> String
prettyShow = render . pretty 0

instance (Pretty a, Pretty b) => Pretty (a,b) where
  pretty n (x,y) = pretty n x <> ": " <> pretty n y

-- Pretty-print collections

class Pretties a where
    pretties :: Nat -> a -> [Doc]

instance Pretty a => Pretties [a] where
  pretties n = map (pretty n)

instance (Pretty a, Pretty b) => Pretties (Map a b) where
  pretties n o = pretties n (toAscList o)

-- Pretty print identifiers

instance Pretty LocalId where
  pretty n (LocalId x) = "x" <> text (show $ n - x - 1)

instance Pretty GlobalId where
  pretty n (GlobalId m) = text $ variableName $ intercalate "_" m

instance Pretty MemberId where
  pretty n (MemberId s) = "\"" <> unescapes s <> "\""

instance Pretty MemberIndex where
  pretty _ (MemberIndex i) = text $ show i

-- Pretty print expressions

instance Pretty Exp where
  pretty n (Self)                 = "exports"
  pretty n (Local x)              = pretty n x
  pretty n (Global m)             = pretty n m
  pretty n (Undefined)            = "undefined"
  pretty n (Null)                 = "null"
  pretty n (String s)             = "\"" <> unescapes s <> "\""
  pretty n (Char c)               = "\"" <> unescapes [c] <> "\""
  pretty n (Integer x)            = "agdaRTS.primIntegerFromString(\"" <> text (show x) <> "\")"
  pretty n (Double x)             = text $ show x
  pretty n (Lambda x e)           =
    mparens (x /= 1) (hsep $ punctuate "," (pretties (n+x) (map LocalId [x-1, x-2 .. 0]))) <>
    " => " <> block (n+x) e
  pretty n (Object o) | null o    = "{}"
  pretty n (Object o) | otherwise =
    indent ("{" $+$ (vcat $ punctuate "," (pretties n o))) $+$ "}"
  pretty n (Array [])             = "[]"
  pretty n (Array es)             =
    indent ("[" $+$ (vcat $ punctuate "," (pretties n es))) $+$ "]"
  pretty n (Apply f es)           = pretty n f <> "(" <> hsep (punctuate "," (pretties n es)) <> ")"
  pretty n (Lookup e l)           = pretty n e <> "[" <> pretty n l <> "]"
  pretty n (LookupIndex e l)      = pretty n e <> "[" <> pretty n l <> "]"
  pretty n (If e f g)             =
    "(" <> pretty n e <> "? " <> pretty n f <> ": " <> pretty n g <> ")"
  pretty n (PreOp op e)           = "(" <> text op <> " " <> pretty n e <> ")"
  pretty n (BinOp e op f)         = "(" <> pretty n e <> " " <> text op <> " " <> pretty n f <> ")"
  pretty n (Const c)              = text c
  pretty n (PlainJS js)           = "(" <> text js <> ")"

block :: Nat -> Exp -> Doc
block n e
  | doNest e  = indent ("(" $+$ pretty n e) $+$ ")"
  | otherwise = pretty n e
  where
    doNest Lambda{} = False
    doNest _ = True

modname :: GlobalId -> Doc
modname (GlobalId ms) = text $ "\"" ++ intercalate "." ms ++ "\""


exports :: Nat -> Set [MemberId] -> [Export] -> Doc
exports n lss [] = ""
exports n lss (Export ls e : es) | member (init ls) lss =
  "exports[" <> hcat (punctuate "][" (pretties n ls)) <> "] = " <> indent (pretty n e) <> ";" $+$
  exports n (insert ls lss) es
exports n lss (Export ls e : es) | otherwise =
  exports n lss (Export (init ls) (Object empty) : Export ls e : es)

instance Pretty Module where
  pretty n (Module m es ex) =
    imports
      $+$ exports n (singleton []) es
      $+$ maybe "" (pretty n) ex
    where
      js = toList (globals es)
      imports = vcat $
            ["var agdaRTS = require(\"agda-rts\");"] ++
            ["var " <> indent (pretty n e) <> " = require(" <> modname e <> ");"
            | e <- js]

variableName :: String -> String
variableName s = if isValidJSIdent s then "z_" ++ s else "h_" ++ show (hashString s)

-- | Check if a string is a valid JS identifier. The check ignores keywords
-- as we prepend z_ to our identifiers. The check
-- is conservative and may not admit all valid JS identifiers.
isValidJSIdent :: String -> Bool
isValidJSIdent s = matchTest regex s
  where
    regex :: Regex
    regex = makeRegex ("^[a-zA-Z_$][0-9a-zA-Z_$]*$" :: String)
