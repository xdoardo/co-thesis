------------------------------------------------------------------------
-- Functional semantics for boolean expressions in Imp
------------------------------------------------------------------------
module Imp.Semantics.BigStep.Functional.Bool where 

open import Data.Maybe
open import Imp.Syntax 
open import Imp.Semantics.BigStep.Functional.Arith
open import Data.Bool using (Bool ; _∧_ ; _∨_ ) renaming (not to bnot)
open import Data.Integer using (_≤ᵇ_ ; ℤ)
---

private 
 zeq : ℤ -> ℤ -> Bool 
 zeq x x₁ = (x ≤ᵇ x₁) ∧ (x₁ ≤ᵇ x)

 zle : ℤ -> ℤ -> Bool
 zle x x₁ = (bnot (zeq x x₁)) ∧ (x ≤ᵇ x₁)

beval : ∀ (b : BExp) (s : Store) -> Maybe Bool
beval (const c) s = just c 
beval (le a₁ a₂) s = do
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
