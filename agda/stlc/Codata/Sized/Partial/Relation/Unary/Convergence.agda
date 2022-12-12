------------------------------------------------------------------------
-- Unary convergence predicate for partial types 
------------------------------------------------------------------------

module Codata.Sized.Partial.Relation.Unary.Convergence where

open import Size
open import Data.Maybe
open import Codata.Sized.Thunk
open import Data.Product using (∃)
open import Codata.Sized.Delay hiding (_⇓)
open import Codata.Sized.Partial.Bisimilarity
open import Codata.Sized.Partial.Relation.Unary.All
open import Function.Equivalence using (_⇔_ ; equivalence)
open import Codata.Sized.Partial.Relation.Binary.Convergence 
---

_⇓ : ∀ {a} {A : Set a} (x : Delay {a} (Maybe A) ∞) → Set a
x ⇓ = ∃ λ a → x ⇓ a

≈-⇓⇓ : ∀ {a} {A : Set a} {x y : Delay (Maybe A) ∞} {i} -> (i ⊢ x ≈ y) ⇔ (x ⇓ ⇔ y ⇓)
≈-⇓⇓ {_} {A} = equivalence (λ x≈y -> ?) (h₂ _ _)
 where
  h₂ : ∀ {a} {A : Set a} {i} (x y : Delay (Maybe A) ∞) -> (x ⇓ ⇔ y ⇓) -> (i ⊢ x ≈ y)
  h₂ (now x) y x⇓⇔y⇓ = ? -- We need transitivity of weak bisimilarity
  h₂ (later x) y x⇓⇔y⇓ = ?
