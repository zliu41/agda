{-# OPTIONS_GHC -fwarn-missing-signatures #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UnicodeSyntax         #-}

module Agda.TypeChecking.SizedTypes.Utils where

import Control.Applicative
import Data.Functor
import qualified Debug.Trace as Debug
import Agda.Utils.Function

debug ∷ Bool
debug = False

trace ∷ String → a → a
trace  s = applyWhen debug $ Debug.trace s

traceM ∷ Applicative f ⇒ String → f ()
traceM s = trace s $ pure ()

($>) ∷ Functor f ⇒ f b → a → f a
($>) = flip (<$)

class Eq a => Top a where
  top   :: a
  isTop :: a -> Bool
  isTop = (==top)

class Plus a b c where
  plus :: a -> b -> c

class MeetSemiLattice a where
  meet :: a -> a -> a

-- | Semiring with idempotent '+' == dioid
class (MeetSemiLattice a, Top a) => Dioid a where
  compose     :: a -> a -> a  -- ^ E.g. +
  unitCompose :: a            -- ^ neutral element of @compose@, e.g. zero
