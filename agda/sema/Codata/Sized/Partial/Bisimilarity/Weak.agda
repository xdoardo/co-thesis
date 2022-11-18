------------------------------------------------------------------------
-- Strong bisimilarity for the partiality monad 
------------------------------------------------------------------------

module Codata.Sized.Partial.Bisimilarity.Weak where 

open import Size
open import Data.Maybe
open import Codata.Sized.Thunk
open import Codata.Sized.Delay hiding (never)
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)


data Bisim {a b r} {A : Set a} {B : Set b} (R : A → B → Set r) i :
           (xs : Delay (Maybe A) ∞) (ys : Delay (Maybe B) ∞) → Set (a ⊔ b ⊔ r) where
  nown   : Bisim R i (now nothing)  (now nothing)
  nowj   : ∀ {x y} → R x y → Bisim R i (now (just x)) (now (just y))
  later : ∀ {xs ys} → Thunk^R (Bisim R) i xs ys → Bisim R i (later xs) (later ys)
  laterₗ : ∀ {xs ys} → Bisim R i (force xs) ys → Bisim R i (later xs) ys
  laterᵣ : ∀ {xs ys} → Bisim R i xs (force ys) → Bisim R i xs (later ys)

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

--  @TODO (ecmm) : I think this won't budge.
--  transitive : Trans P Q R → ∀ {i} → Trans (Bisim P i) (Bisim Q i) (Bisim R i)
--  transitive trans^PQR nown nown = nown
--  transitive trans^PQR nown (laterᵣ b^23) = laterᵣ (transitive trans^PQR nown b^23)
--  transitive trans^PQR (nowj x) (nowj x₁) = nowj (trans^PQR x x₁) 
--  transitive trans^PQR (nowj x) (laterᵣ b^23) = laterᵣ (transitive trans^PQR (nowj x) b^23)
--  transitive trans^PQR (later x) (later x₁) = later (λ where .force -> transitive trans^PQR (force x) (force x₁))
--  transitive trans^PQR  (later x) (laterₗ b^23) = ? 
--  transitive trans^PQR (later x) (laterᵣ b^23) = laterᵣ (transitive trans^PQR (later x) b^23)
--  transitive trans^PQR (laterₗ b^12) nown = laterₗ (transitive trans^PQR b^12 nown)
--  transitive trans^PQR (laterₗ b^12) (nowj x) = laterₗ (transitive trans^PQR b^12 (nowj x))
--  transitive trans^PQR (laterₗ b^12) (later x) = laterₗ (transitive trans^PQR b^12 (later x))
--  transitive trans^PQR (laterₗ b^12) (laterₗ b^23) = laterₗ (transitive trans^PQR b^12 (laterₗ b^23))
--  transitive trans^PQR {i} (laterᵣ b^12) (later x) = ? 
--  transitive trans^PQR (laterₗ b^12) (laterᵣ b^23) = later (λ where .force -> transitive trans^PQR (b^12) (b^23))
--  transitive trans^PQR (laterᵣ b^12) (laterₗ b^23) = transitive trans^PQR b^12 b^23
--  transitive trans^PQR (laterᵣ b^12) (laterᵣ b^23) = laterᵣ (transitive trans^PQR (laterᵣ b^12) b^23)


-- Pointwise Equality as a Bisimilarity
------------------------------------------------------------------------

module _ {ℓ} {A : Set ℓ} where

 infix 1 _⊢_≈_
 _⊢_≈_ : ∀ i → Delay (Maybe A) ∞ → Delay (Maybe A) ∞ → Set ℓ
 _⊢_≈_ = Bisim _≡_

 refl : ∀ {i} → Reflexive (i ⊢_≈_)
 refl = reflexive Eq.refl

 sym : ∀ {i} → Symmetric (i ⊢_≈_)
 sym = symmetric Eq.sym

-- trans : ∀ {i} → Transitive (i ⊢_≈_)
-- trans = transitive Eq.trans


------------------------------------------------------------------------
-- Examples 
module _ {a b c} {A : Set a} {B : Set b} {C : Set c}
         {r} {P : A → B → Set r} {Q : B → C → Set r} {R : A → C → Set r} where
  open import Codata.Sized.Partial

  fail-refl : ∀ {i} -> i ⊢ (fail {A = A}) ≈ (fail {A = A})
  fail-refl = refl

  never-refl : ∀ {i} -> i ⊢ (never {A = A}) ≈ (never {A = A})
  never-refl = refl

-- Weak examples 
  postpone : ∀ {i} -> (x : Delay {a} (Maybe A) i) -> Thunk (Delay {a} (Maybe A)) i
  force (postpone x) = x
  
  _ : ∀ {i x} -> i ⊢ (later (postpone x)) ≈ x
  _ = laterₗ (refl)
