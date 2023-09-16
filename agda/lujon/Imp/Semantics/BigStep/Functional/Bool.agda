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
beval (le a₁ a₂) s = aeval a₁ s >>= λ v₁ -> aeval a₂ s >>= λ v₂ -> just (v₁ ≤ᵇ v₂)
beval (not b) s = beval b s >>= λ b -> just (bnot b) 
beval (and b₁ b₂) s = beval b₁ s >>= λ b₁ -> beval b₂ s >>= λ b₂ -> just (b₁ ∧ b₂)
