------------------------------------------------------------------------
-- Unary convergence predicate for partial types 
------------------------------------------------------------------------

module Codata.Sized.Partial.Relation.Unary.Convergence where

open import Size
open import Data.Or
open import Data.Maybe
open import Data.Product
open import Codata.Sized.Thunk
open import Data.Product using (∃)
open import Codata.Sized.Delay hiding (_⇓ ; bind)
open import Codata.Sized.Partial.Effectful
open import Codata.Sized.Partial.Bisimilarity
open import Relation.Binary.PropositionalEquality
open import Codata.Sized.Partial.Relation.Unary.All
open import Function.Equivalence using (_⇔_ ; equivalence)
open import Codata.Sized.Partial.Relation.Binary.Convergence 
---

_⊢_⇓  : ∀ {a} {A : Set a} (i : Size) (x : Delay {a} (Maybe A) i) → Set a
i ⊢ x ⇓ =  ∃ λ a -> i ⊢ x ⇓ a 


---- @TODO
--postulate
-- ≈-⇓⇓ : ∀ {a} {A : Set a} {x y : Delay (Maybe A) ∞} {i} -> (i ⊢ x ≈ y) ⇔ (x ⇓ ⇔ y ⇓)
-- ≈-⇑⇑  : ∀ {a} {A : Set a} {x y : Delay (Maybe A) ∞} {i} -> (i ⊢ x ≈ y) ⇔ (x ⇑ ⇔ y ⇑)
