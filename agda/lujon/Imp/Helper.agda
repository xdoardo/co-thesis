
module Imp.Helper where

open import Size
open import Data.Maybe
open import Imp.Syntax
open import Codata.Sized.Delay
open import Codata.Sized.Thunk
open import Codata.Sized.Delay.WeakBisimilarity
open import Codata.Sized.FailingDelay.Effectful
open import Relation.Binary.PropositionalEquality
open import Imp.Semantics.BigStep.Functional
---
module _ {a} {A : Set a} where

 while-unroll : ∀ (c : Command) (b : BExp) (s : Store) (f : ∀ {v} (h : ∞ ⊢ ceval (while b c) s ≋ v) -> A) -> A
 while-unroll c b s f = {! !}
