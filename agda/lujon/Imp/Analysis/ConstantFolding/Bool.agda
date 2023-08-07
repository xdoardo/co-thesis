------------------------------------------------------------------------
-- Constant folding for boolean expressions of Imp
------------------------------------------------------------------------
module Imp.Analysis.ConstantFolding.Bool where

open import Data.Unit
open import Data.Maybe
open import Imp.Syntax
open import Data.Integer
open import Data.Bool renaming (not to lnot)
open import Imp.Analysis.ConstantFolding.Arith
open import Data.Integer.Properties as ℤ-Properties
open import Data.Nat using () renaming (suc to ℕ-suc)
---

-- Constant folding (and constant propagation) of arithmetic expressions
bfold : (b : BExp) -> (s : Store) -> BExp
bfold (const b) _ = const b
bfold (le a₁ a₂) s with (afold a₁ s) | (afold a₂ s)
... | const n | const n₁ = const (n ≤ᵇ n₁) 
... | a₁' | a₂' = le a₁' a₂'
bfold (not b) s with (bfold b s) 
... | const b₁ = const (lnot b₁) 
... | b' = not b'
bfold (and b₁ b₂) s with (bfold b₁ s) | (bfold b₂ s)
... | const n₁ | const n₂ = const (n₁ ∧ n₂) 
... | b₁ | b₂ = and b₁ b₂ 

------------------------------------------------------------------------
-- Properties of constant folding 
------------------------------------------------------------------------
module _ where
 open import Relation.Binary.PropositionalEquality
 open import Imp.Semantics.BigStep.Functional
 open import Imp.Syntax.Ident
 open ≡-Reasoning 

 -- Folding preserves semantics.
 bfold-sound : ∀ b {s t : Store} {p : t ≅ s} -> (beval b s ≡ beval (bfold b t) s)
 bfold-sound (const b) {s} {t} {p} = refl
 bfold-sound (le a₁ a₂) {s} {t} {p} 
  rewrite (afold-sound a₁ {s} {t} {p}) 
  rewrite (afold-sound a₂ {s} {t} {p}) 
  with (afold a₁ t) | (afold  a₂ t)
 ... | const n | const n₁ = refl
 ... | const n | var id = refl
 ... | const n | plus v₂ v₃ = refl
 ... | var id | v₂ = refl
 ... | plus v₁ v₃ | v₂ = refl
 bfold-sound (not b) {s} {t} {p} 
  rewrite (bfold-sound b {s} {t} {p})
  with (bfold b t) in eq-bfold-t
 ... | const b₁ = refl
 ... | le a₁ a₂ = refl
 ... | not v = refl
 ... | and v v₁ = refl
 bfold-sound (and b₁ b₂) {s} {t} {p}
  rewrite (bfold-sound b₁ {s} {t} {p}) 
  rewrite (bfold-sound b₂ {s} {t} {p}) 
  with (bfold b₁ t) | (bfold b₂ t) 
 ... | const b | const b₃ = refl
 ... | const b | le a₁ a₂ = refl
 ... | const b | not v₂ = refl
 ... | const b | and v₂ v₃ = refl
 ... | le a₁ a₂ | v₂ = refl
 ... | not v₁ | v₂ = refl
 ... | and v₁ v₃ | v₂ = refl
