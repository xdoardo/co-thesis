------------------------------------------------------------------------
-- Functional semantics for arithmetic expressions in Imp
------------------------------------------------------------------------
module Imp.Semantics.BigStep.Functional.Arith where 

open import Data.Unit
open import Data.Maybe 
open import Imp.Syntax
open import Data.Integer 
open import Data.Bool hiding (_≟_)
open import Relation.Nullary using (¬_)
open import Data.Integer.Properties as ℤ-Properties
open import Data.Nat using () renaming (suc to ℕ-suc)
--

aeval : ∀ (a : AExp) (s : Store) -> Maybe ℤ
aeval (const x) s = just x
aeval (var x) s = s x
aeval (plus a a₁) s = aeval a s >>= λ v₁ -> aeval a₁ s >>= λ v₂ -> just (v₁ + v₂)
