---------------------------------------------------------------------------
-- The Partiality monad
---------------------------------------------------------------------------
module Monad.PartialityMonad where

open import Category.Monad
open import Function 
open import Lambda.Syntax
import Monad.DelayMonad as DelayMonad
import Data.Maybe as MaybeMonad
import Data.Maybe.Categorical as MaybeCategorical

PartialityFunctor : RawMonad  (DelayMonad.Delay ∘ MaybeMonad.Maybe)
PartialityFunctor = MaybeCategorical.monadT DelayMonad.delayMonad
