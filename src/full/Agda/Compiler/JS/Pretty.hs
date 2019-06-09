{-# LANGUAGE OverloadedStrings #-}
module Agda.Compiler.JS.Pretty where

import Data.List ( intercalate )
import Data.String ( IsString (fromString) )
import Data.Set ( Set, toList, singleton, insert, member )
import Data.Map ( Map, toAscList )
import Text.Regex.TDFA (makeRegex, matchTest, Regex)

import Agda.Syntax.Common ( Nat )
import Agda.Utils.Hash

import Agda.Compiler.JS.Syntax hiding (exports)

-- Pretty-print a lambda-calculus expression as ECMAScript.

--- The indentation combinators of the pretty library does not fit C-like languages
--- like ECMAScript.
--- A simple pretty printer is implemented with a better `indent` and punctuation compaction.

data Doc
    = Doc String
    | Indent Int Doc
    | Group Doc
    | Beside Doc Doc
    | Above Doc Doc
    | Enclose Doc Doc Doc
    | Empty

render :: Doc -> String
render = intercalate "\n" . map (uncurry mkIndent) . go 0
  where
    joinBy f [x] (y: ys) = f x y ++ ys
    joinBy f (x:xs) ys = x: joinBy f xs ys
    joinBy f xs ys = xs ++ ys

    mkIndent n "" = ""
    mkIndent n s = replicate n ' ' ++ s

    overlay (i, s) (j, s') | all punctuation (s ++ s') && n > 0 = [(i, s ++ mkIndent n s')]
      where n = j - (i + length s)
    overlay (j, s') (i, s) | all punctuation (s ++ s') && n > 0 = [(i, s' ++ mkIndent n s)]
      where n = j - (i + length s)
    overlay a b = [a, b]

    punctuation = (`elem` ("(){}[];:, " :: String))

    go i Empty = []
    go i (Doc s) = [(i, s)]
    go i (Beside d d') = joinBy (\(i, s) (_, s') -> [(i, s ++ s')]) (go i d) (go i d')
    go i (Above d d') = joinBy overlay (go i d) (go i d')
    go i (Indent j d) = go (i+j) d
    go i (Enclose open close d) = go i $ Group $ Above open $ Above d close
    go i (Group d)
        | size ss < 40 = compact ss
        | otherwise    = ss
      where
        ss = go i d
        size = sum . map (length . snd)
        compact [] = []
        compact ((i, x): xs) = [(i, x ++ concatMap snd xs)]

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

group :: Doc -> Doc
group = Group

indentBy :: Int -> Doc -> Doc
indentBy i Empty = Empty
indentBy i (Indent j d) = Indent (i+j) d
indentBy i d = Indent i d

enclose :: Doc -> Doc -> Doc -> Doc
enclose open close (Enclose o c d) = Enclose (open <> o) (c <> close) d
enclose open close (Indent _ (Enclose o c d)) = Enclose (open <> o) (c <> close) d
enclose open close d = Enclose open close d

----------------------------------------------------------------------------------------------

indent :: Doc -> Doc
indent = indentBy 2

hcat :: [Doc] -> Doc
hcat = foldr (<>) mempty

vcat :: [Doc] -> Doc
vcat = foldr ($+$) mempty

punctuate :: Doc -> [Doc] -> Doc
punctuate _ []     = mempty
punctuate p (x:xs) = indent $ vcat $ go x xs
                   where go y []     = [y]
                         go y (z:zs) = (y <> p) : go z zs

parens, brackets, braces :: Doc -> Doc
parens   = enclose "(" ")"
brackets = enclose "[" "]"
braces   = enclose "{" "}"

-- | Apply 'parens' to 'Doc' if boolean is true.
mparens :: Bool -> Doc -> Doc
mparens True  d = parens d
mparens False d = d

----------------------------------------------------------------------------------------------

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

-- Pretty print expressions

instance Pretty Exp where
  pretty n (Self)            = "exports"
  pretty n (Local x)         = pretty n x
  pretty n (Global m)        = pretty n m
  pretty n (Undefined)       = "undefined"
  pretty n (Null)            = "null"
  pretty n (String s)        = "\"" <> unescapes s <> "\""
  pretty n (Char c)          = "\"" <> unescapes [c] <> "\""
  pretty n (Integer x)       = "agdaRTS.primIntegerFromString(\"" <> text (show x) <> "\")"
  pretty n (Double x)        = text $ show x
  pretty n (Lambda x e)      =
    mparens (x /= 1) (punctuate "," (pretties (n+x) (map LocalId [x-1, x-2 .. 0]))) <>
    " => " <> block (n+x) e
  pretty n (Object o)        = braces $ punctuate "," $ pretties n o
  pretty n (Apply f es)      = pretty n f <> parens (punctuate "," $ pretties n es)
  pretty n (Lookup e l)      = pretty n e <> brackets (pretty n l)
  pretty n (If e f g)        = parens $ pretty n e <> "? " <> pretty n f <> ": " <> pretty n g
  pretty n (PreOp op e)      = parens $ text op <> " " <> pretty n e
  pretty n (BinOp e op f)    = parens $ pretty n e <> " " <> text op <> " " <> pretty n f
  pretty n (Const c)         = text c
  pretty n (PlainJS js)      = parens $ text js

block :: Nat -> Exp -> Doc
block n e = mparens (doNest e) $ pretty n e
  where
    doNest Object{} = True
    doNest _ = False

modname :: GlobalId -> Doc
modname (GlobalId ms) = text $ "\"" ++ intercalate "." ms ++ "\""


exports :: Nat -> Set [MemberId] -> [Export] -> Doc
exports n lss [] = ""
exports n lss (Export ls e : es) | member (init ls) lss =
  "exports" <> hcat (map brackets (pretties n ls)) <> " = " <> indent (pretty n e) <> ";" $+$
  exports n (insert ls lss) es
exports n lss (Export ls e : es) | otherwise =
  exports n lss (Export (init ls) (Object mempty) : Export ls e : es)

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
