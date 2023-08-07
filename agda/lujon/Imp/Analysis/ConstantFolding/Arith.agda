------------------------------------------------------------------------
-- Constant folding for arithmetic expressions of Imp
------------------------------------------------------------------------
module Imp.Analysis.ConstantFolding.Arith where

open import Data.Unit
open import Data.Maybe
open import Data.Integer
open import Imp.Syntax
open import Data.Integer.Properties as ℤ-Properties
open import Data.Nat using () renaming (suc to ℕ-suc)
---

-- Constant folding (and constant propagation) of arithmetic expressions
afold : (a : AExp) -> (s : Store) -> AExp
afold (const x) _ = const x 
afold (var id) s with (s id)  
... | just v = const v
... | nothing = var id
afold (plus a₁ a₂) s with (afold a₁ s) | (afold a₂ s)
... | const v₁ | const v₂ = const (v₁ + v₂)
... | a₁' | a₂' = plus a₁' a₂'

------------------------------------------------------------------------
-- Properties of constant folding 
------------------------------------------------------------------------
module _ where
 open import Relation.Binary.PropositionalEquality
 open import Imp.Semantics.BigStep.Functional
 open import Imp.Syntax.Ident
 open ≡-Reasoning 

 -- Folding preserves semantics.
 afold-sound : ∀ a {s t : Store} {p : t ≅ s} -> (aeval a s ≡ aeval (afold a t) s)
 afold-sound (const n) = refl
 afold-sound (var id) {s} {t} {p} with (t id) in eq-tid
 ... | nothing = refl
 ... | just x rewrite (p {id} {x} eq-tid) = refl
 afold-sound (plus a₁ a₂) {s} {t} {p} 
  rewrite (afold-sound a₁ {s} {t} {p})
  rewrite (afold-sound a₂ {s} {t} {p})
  with (afold a₁ t) in eq-folda₁ | (afold a₂ t) in eq-folda₂
 ... | const n | const n₁ rewrite eq-folda₁ rewrite eq-folda₂ = refl
 ... | const n | var id = refl
 ... | const n | plus v₂ v₃ = refl
 ... | var id | v₂ = refl
 ... | plus v₁ v₃ | v₂ rewrite eq-folda₁ rewrite eq-folda₂ = refl
