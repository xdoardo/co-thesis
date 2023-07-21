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

_⇑ : ∀ {a} {A : Set a} -> Delay (Maybe A) ∞ -> Set a
x ⇑ = ∀ {i} -> i ⊢ x ≈ never

postulate
 ≈-⇓⇓ : ∀ {a} {A : Set a} {x y : Delay (Maybe A) ∞} {i} -> (i ⊢ x ≈ y) ⇔ (x ⇓ ⇔ y ⇓)
