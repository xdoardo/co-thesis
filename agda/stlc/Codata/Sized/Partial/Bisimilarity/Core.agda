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

data Bisim {a b r} {A : Set a} {B : Set b} (R : A → B → Set r) i :
           (xs : Delay (Maybe A) ∞) (ys : Delay (Maybe B) ∞) → Set (a ⊔ b ⊔ r) where
  nown   : Bisim R i (now nothing)  (now nothing)
  nowj   : ∀ {x y} → R x y → Bisim R i (now (just x)) (now (just y))
  later : ∀ {xs ys} → Thunk^R (Bisim R) i xs ys → Bisim R i (later xs) (later ys)
  laterₗ : ∀ {xs ys} → Bisim R i (force xs) ys → Bisim R i (later xs) ys
  laterᵣ : ∀ {xs ys} → Bisim R i xs (force ys) → Bisim R i xs (later ys)

module Equivalence where
 module _ {a r} {A : Set a} {R : A → A → Set r} where
 
   reflexive : Reflexive R → ∀ {i} → Reflexive (Bisim R i)
   reflexive refl^R {i} {now (just x)} = nowj refl^R
   reflexive refl^R {i} {now nothing} = nown 
   reflexive refl^R {i} {later x} = later λ where .force -> reflexive (refl^R) 
 
 module _ {a b} {A : Set a} {B : Set b}
          {r} {P : A → B → Set r} {Q : B → A → Set r} where
 
 
   symmetric : Sym P Q → ∀ {i} → Sym (Bisim P i) (Bisim Q i)
   symmetric sym^PQ nown = nown 
   symmetric sym^PQ (nowj x) = nowj (sym^PQ x)
   symmetric sym^PQ (later x) = later λ where .force -> symmetric (sym^PQ) (force x)
   symmetric sym^PQ {i} (laterₗ x ) = laterᵣ (symmetric sym^PQ x)
   symmetric sym^PQ (laterᵣ x) = laterₗ (symmetric sym^PQ x)
 
 module _ {a b c} {A : Set a} {B : Set b} {C : Set c}
          {r} {P : A → B → Set r} {Q : B → C → Set r} {R : A → C → Set r} where

-- Pointwise Equality as a Bisimilarity
------------------------------------------------------------------------

module _ {ℓ} {A : Set ℓ} where
 open Equivalence
 infix 1 _⊢_≈_
 _⊢_≈_ : ∀ i → Delay (Maybe A) ∞ → Delay (Maybe A) ∞ → Set ℓ
 _⊢_≈_ = Bisim _≡_

 refl : ∀ {i} → Reflexive (i ⊢_≈_)
 refl = reflexive Eq.refl

 sym : ∀ {i} → Symmetric (i ⊢_≈_)
 sym = symmetric Eq.sym
