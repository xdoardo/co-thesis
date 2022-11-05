---------------------------------------------------------------------------
-- The Partiality monad
---------------------------------------------------------------------------
module Monad.PartialityMonad where

open import Category.Monad
open import Function 
open import Lambda.Syntax
open import Agda.Builtin.Size
open import Monad.DelayMonad using (Delay ; delayMonad)
open import Monad.SizedMaybeMonad using (Maybe ; maybeMonadT)

PartialityMonad : ∀ {i : Size} -> RawMonad (Delay {i} ∘ (Maybe {i}))
PartialityMonad {i} = maybeMonadT delayMonad
