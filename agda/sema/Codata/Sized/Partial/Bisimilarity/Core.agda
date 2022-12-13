------------------------------------------------------------------------
-- Weak bisimilarity for the partiality monad 
------------------------------------------------------------------------

module Codata.Sized.Partial.Bisimilarity.Core where 

open import Size
open import Level
open import Data.Maybe
open import Relation.Binary
open import Codata.Sized.Thunk
open import Codata.Sized.Delay hiding (never ; _⇓)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
---

data Bisim {a b r} {A : Set a} {B : Set b} (R : A -> B -> Set r) i :
           (xs : Delay (Maybe A) ∞) (ys : Delay (Maybe B) ∞) -> Set (a ⊔ b ⊔ r) where
  nown   : Bisim R i (now nothing)  (now nothing)
  nowj   : ∀ {x y} -> R x y -> Bisim R i (now (just x)) (now (just y))
  later : ∀ {xs ys} -> Thunk^R (Bisim R) i xs ys -> Bisim R i (later xs) (later ys)
  laterₗ : ∀ {xs ys} -> Bisim R i (force xs) ys -> Bisim R i (later xs) ys
  laterᵣ : ∀ {xs ys} -> Bisim R i xs (force ys) -> Bisim R i xs (later ys)



-- Pointwise Equality as a Bisimilarity
module _ {ℓ} {A : Set ℓ} where

 infix 1 _⊢_≈_
 _⊢_≈_ : ∀ i → Delay (Maybe A) ∞ → Delay (Maybe A) ∞ → Set ℓ
 _⊢_≈_ = Bisim _≡_

 
module _ {a r b} {A : Set a} {B : Set b} {R : A -> B -> Set r} where
 
 laterʳ⁻¹ : ∀  {i} {j : Size< i} {x : Delay (Maybe A) ∞} {y} -> Bisim R i x (later y) -> Bisim R j x (force y) 
 laterʳ⁻¹ (later x) = laterₗ (force x)
 laterʳ⁻¹ (laterᵣ x) = x
 laterʳ⁻¹ (laterₗ x) = laterₗ (laterʳ⁻¹ x)  

 laterˡ⁻¹ : ∀ {i} {x} {y : Delay (Maybe B) ∞} -> Bisim R (↑ i) (later x) y -> Bisim R i (force x) y
 laterˡ⁻¹ (later x) = laterᵣ (force x) 
 laterˡ⁻¹ (laterₗ x) = x 
 laterˡ⁻¹ (laterᵣ x) = laterᵣ (laterˡ⁻¹ x) 
 
 later⁻¹ : ∀ {i} {x y} -> Bisim R (↑ i) (later x) (later y) -> Bisim R i (force x) (force y)
 later⁻¹ (later x) = force x
 later⁻¹ (laterₗ x) = laterʳ⁻¹ x
 later⁻¹ (laterᵣ x) = laterˡ⁻¹ x
