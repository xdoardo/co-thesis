------------------------------------------------------------------------
-- Pure constant folding (no constant propagation) for boolean expressions of Imp
------------------------------------------------------------------------
module Imp.Analysis.PureFolding.Bool where

open import Data.Bool renaming (not to lnot)
open import Data.Unit
open import Data.Maybe
open import Imp.Syntax
open import Data.Integer
open import Imp.Analysis.PureFolding.Arith
open import Data.Integer.Properties as ℤ-Properties
open import Data.Nat using () renaming (suc to ℕ-suc)
---

-- Pure constant folding of boolean expressions
bpfold : (b : BExp) -> BExp
bpfold (const b) = const b 
bpfold (le a₁ a₂) with (apfold a₁) | (apfold a₂)
... | const n₁ | const n₂ = const (n₁ ≤ᵇ n₂ )
... | a₁ | a₂ = le a₁ a₂ 
bpfold (not b) with (bpfold b) 
... | const n = const (lnot n) 
... | b = not b
bpfold (and b₁ b₂) with (bpfold b₁) | (bpfold b₂)
... | const n₁ | const n₂ = const (n₁ ∧ n₂) 
... | b₁ | b₂ = and b₁ b₂ 

------------------------------------------------------------------------
-- Properties of constant folding 
------------------------------------------------------------------------
module _ where
 open import Imp.Semantics.BigStep.Functional 
 open import Relation.Binary.PropositionalEquality
 open ≡-Reasoning 

 -- Folding preserves semantics.
 bpfold-safe : ∀ b s  -> (beval b s ≡ beval (bpfold b) s)
 bpfold-safe (const b) s  = refl
 bpfold-safe (le a₁ a₂) s rewrite (apfold-safe a₁ s) rewrite (apfold-safe a₂ s) 
  with (apfold a₁) | (apfold a₂)
 ... | const n | const n₁ = refl
 ... | const n | var id = refl
 ... | const n | plus v₂ v₃ = refl
 ... | var id | v₂ = refl
 ... | plus v₁ v₃ | v₂ = refl
 bpfold-safe (not b) s rewrite (bpfold-safe b s) with (bpfold b) 
 ... | const b₁ = refl
 ... | le a₁ a₂ = refl
 ... | not v = refl
 ... | and v v₁ = refl
 bpfold-safe (and b₁ b₂) s rewrite (bpfold-safe b₁ s) rewrite (bpfold-safe b₂ s) 
  with (bpfold b₁) | (bpfold b₂) 
 ... | const b | const b₃ = refl
 ... | const b | le a₁ a₂ = refl
 ... | const b | not v₂ = refl
 ... | const b | and v₂ v₃ = refl
 ... | le a₁ a₂ | v₂ = refl
 ... | not v₁ | v₂ = refl
 ... | and v₁ v₃ | v₂ = refl
