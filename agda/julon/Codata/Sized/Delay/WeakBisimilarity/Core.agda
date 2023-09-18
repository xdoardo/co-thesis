------------------------------------------------------------------------
-- Weak bisimilarity for the partiality monad 
------------------------------------------------------------------------

module Codata.Sized.Delay.WeakBisimilarity.Core where 

open import Size
open import Level
open import Data.Maybe
open import Relation.Binary
open import Codata.Sized.Thunk
open import Codata.Sized.Delay hiding (never ; _⇓)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
---

data WeakBisim {a b r} {A : Set a} {B : Set b} (R : A -> B -> Set r) i :
           (xs : Delay A ∞) (ys : Delay B ∞) -> Set (a ⊔ b ⊔ r) where
  now   : ∀ {x y} -> R x y -> WeakBisim R i (now x) (now y)
  later : ∀ {xs ys} -> Thunk^R (WeakBisim R) i xs ys -> WeakBisim R i (later xs) (later ys)
  laterₗ : ∀ {xs ys} -> WeakBisim R i (force xs) ys -> WeakBisim R i (later xs) ys
  laterᵣ : ∀ {xs ys} -> WeakBisim R i xs (force ys) -> WeakBisim R i xs (later ys)

-- Infinite sized WeakBisimilarity
infix 4 _≈<_>_

_≈<_>_ : ∀ {a b r} {A : Set a} {B : Set b}  
       -> Delay A ∞ -> (R : A -> B -> Set r) -> Delay B ∞ -> Set (a ⊔ b ⊔ r)
x ≈< R > x₁ = WeakBisim R ∞ x x₁ 

-- Pointwise Equality as a WeakBisimilarity
module _ {ℓ} {A : Set ℓ} where

 infix 1 _⊢_≋_
 _⊢_≋_ : ∀ i → Delay A ∞ → Delay A ∞ → Set ℓ
 _⊢_≋_ = WeakBisim _≡_
