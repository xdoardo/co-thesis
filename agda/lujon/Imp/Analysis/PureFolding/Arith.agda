------------------------------------------------------------------------
-- Pure constant folding (no constant propagation) for arithmetic expressions of Imp
------------------------------------------------------------------------
module Imp.Analysis.PureFolding.Arith where

open import Data.Unit
open import Data.Maybe
open import Data.Integer
open import Imp.Syntax
open import Data.Integer.Properties as ℤ-Properties
open import Data.Nat using () renaming (suc to ℕ-suc)
---

-- Constant folding of arithmetic expressions
apfold : (a : AExp) -> AExp
apfold (const x) = const x 
apfold (var id) = var id
apfold (plus a₁ a₂) with (apfold a₁) | (apfold a₂)
... | const v₁ | const v₂ = const (v₁ + v₂)
... | a₁' | a₂' = plus a₁' a₂'

------------------------------------------------------------------------
-- Properties of pure constant folding 
------------------------------------------------------------------------
module _ where
 open import Imp.Semantics.BigStep.Functional
 open import Relation.Binary.PropositionalEquality
 open ≡-Reasoning 

 -- Pure constant folding preserves semantics.
 apfold-safe : ∀ a s -> (aeval a s ≡ aeval (apfold a) s)
 apfold-safe (const n) _ = refl
 apfold-safe (var id) _ = refl
 apfold-safe (plus a₁ a₂) s 
  rewrite (apfold-safe a₁ s) 
  rewrite (apfold-safe a₂ s)  
  with (apfold a₁) in eq-a₁ | (apfold a₂) in eq-a₂
 ... | const n | const n₁  = refl
 ... | const n | var id     = refl
 ... | const n | plus v₂ v₃ = refl
 ... | var id     | v₂ = refl
 ... | plus v₁ v₃ | v₂ = refl
