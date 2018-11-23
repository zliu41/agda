{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Agda.Compiler.JS.Syntax where

import Data.Maybe ( catMaybes )
import Data.Map ( Map )
import qualified Data.Map as Map

import Data.Set ( Set, empty, singleton, union )
import qualified Data.Set as Set

import Agda.Syntax.Common ( Nat )

-- An untyped lambda calculus with records,
-- and a special self-binder for recursive declarations

data Exp =
  Self |
  Local LocalId |
  Global GlobalId |
  Undefined |
  Null |
  String String |
  Char Char |
  Integer Integer |
  Double Double |
  Lambda Nat Exp |
  Object (Map MemberId Exp) |
  Array [(Comment, Exp)] |
  Apply Exp [Exp] |
  Lookup Exp MemberId |
  If Exp Exp Exp |
  BinOp Exp String Exp |
  PreOp String Exp |
  Const String |
  PlainJS String -- ^ Arbitrary JS code.
  deriving (Show, Eq)

-- Local identifiers are named by De Bruijn indices.
-- Global identifiers are named by string lists.
-- Object members are named by strings.

newtype LocalId = LocalId Nat
  deriving (Eq, Ord, Show)

newtype GlobalId = GlobalId [String]
  deriving (Eq, Ord, Show)

data MemberId
    = MemberId String
    | MemberIndex Int Comment
  deriving (Eq, Ord, Show)

newtype Comment = Comment String
  deriving (Show, Semigroup, Monoid)

instance Eq Comment where _ == _ = True
instance Ord Comment where compare _ _ = EQ

-- The top-level compilation unit is a module, which names
-- the GId of its exports, and a list of definitions

data Export = Export { expName :: [MemberId], defn :: Exp }
  deriving Show

data Module = Module { modName :: GlobalId, exports :: [Export], postscript :: Maybe Exp }
  deriving Show

-- Note that modules are allowed to be recursive, via the Self expression,
-- which is bound to the exported module.

class Uses a where
  uses :: Bool{-go under lambdas-} -> a -> Set (Maybe GlobalId, [MemberId])

instance Uses a => Uses [a] where
  uses lam = foldr (union . uses lam) empty

instance Uses a => Uses (Map k a) where
  uses lam = Map.foldr (union . uses lam) empty

instance Uses Exp where
  uses True (Lambda n e)   = uses True e
  uses lam (Object o)     = uses lam o
  uses lam (Array es)     = uses lam $ map snd es
  uses lam (Apply e es)   = uses lam e `union` uses lam es
  uses lam (Lookup e l)   = uses' e [l] where
      uses' Self         ls = singleton (Nothing, ls)
      uses' (Global i)   ls = singleton (Just i, ls)
      uses' (Lookup e l) ls = uses' e (l : ls)
      uses' e            ls = uses lam e
  uses lam (If e f g)     = uses lam e `union` uses lam f `union` uses lam g
  uses lam (BinOp e op f) = uses lam e `union` uses lam f
  uses lam (PreOp op e)   = uses lam e
  uses _ e              = empty

instance Uses Export where
  uses lam (Export _ e) = uses lam e

instance Uses Module where
  uses lam (Module m es _) = uses lam es

-- Top-level uses of the form exports.l1....lN.
globals :: Uses a => a -> Set GlobalId
globals = Set.fromList . catMaybes . map fst . Set.toList . uses True
