------------------------------------------------------------------------
-- Equational reasoning for weak bisimilarity 
------------------------------------------------------------------------

module Codata.Sized.Partial.Bisimilarity.Reasoning where

open import Size
open import Data.Maybe
open import Codata.Sized.Delay
open import Codata.Sized.Partial.Bisimilarity.Core
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
---

-- infix  2 _∎
infixr 2 _≡⟨_⟩_ _≈⟨_⟩_

_≡⟨_⟩_ : ∀ {a} {A : Set a} {k} x {y z : Delay (Maybe A) ∞} {i} → x ≡ y → Bisim i k y z → Bisim i k x z
_ ≡⟨ Eq.refl ⟩ y≈z = y≈z 

_≈⟨_⟩_ : ∀ {a} {A : Set a} x {y z : Delay (Maybe A) ∞} {i} → (i ⊢ x ≈ y) → (i ⊢ y ≈ z) → (i ⊢ x ≈ z)
_ ≈⟨ x≈y ⟩ y≈z = ?
