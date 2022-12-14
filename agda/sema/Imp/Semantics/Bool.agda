------------------------------------------------------------------------
-- Functional semantics for boolean expressions in IMP 
------------------------------------------------------------------------
module Imp.Semantics.Bool where 

open import Data.Maybe
open import Imp.Syntax 
open import Imp.Semantics.Arith
open import Data.Bool using (Bool ; _∧_ ; _∨_ ; true) renaming (not to bnot)
open import Data.Integer using (_≤ᵇ_)
---


beval : ∀ (b : BExp) (s : Store) -> Maybe Bool
beval true s = just Bool.true
beval false s = just Bool.false 
beval (eq a₁ a₂) s = do
 v₁ <- aeval a₁ s
 v₂ <- aeval a₂ s
 just ((v₁ ≤ᵇ v₂) ∧ (v₂ ≤ᵇ v₁))
beval (leq a₁ a₂) s = do
 v₁ <- aeval a₁ s
 v₂ <- aeval a₂ s
 just (v₁ ≤ᵇ v₂)
beval (not b) s = do 
 b <- beval b s
 just (bnot b)
beval (and b₁ b₂) s = do
 b₁ <- beval b₁ s
 b₂ <- beval b₂ s
 just (b₁ ∧ b₂)

------------------------------------------------------------------------
-- Lemmas and examples 
------------------------------------------------------------------------

module _ where 
