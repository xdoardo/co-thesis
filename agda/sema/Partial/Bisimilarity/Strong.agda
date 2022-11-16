------------------------------------------------------------------------
-- Strong bisimilarity for the partiality monad 
------------------------------------------------------------------------

module Partial.Bisimilarity.Strong where 

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

module _ {a r} {A : Set a} {R : A → A → Set r} where

 reflexive : Reflexive R → ∀ {i} → Reflexive (Bisim R i)
 reflexive refl^R {i} {now (just x)} = nowj refl^R
 reflexive refl^R {i} {now nothing} = nown 
 reflexive refl^R {i} {later x} = later λ where .force -> reflexive refl^R

module _ {a b} {A : Set a} {B : Set b}
         {r} {P : A → B → Set r} {Q : B → A → Set r} where

 symmetric : Sym P Q → ∀ {i} → Sym (Bisim P i) (Bisim Q i)
 symmetric sym^PQ (nowj x) = nowj (sym^PQ x) 
 symmetric sym^PQ nown = nown 
 symmetric sym^PQ (later x) = later λ where .force → symmetric sym^PQ (x .force)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c}
         {r} {P : A → B → Set r} {Q : B → C → Set r} {R : A → C → Set r} where

 transitive : Trans P Q R → ∀ {i} → Trans (Bisim P i) (Bisim Q i) (Bisim R i)
 transitive trans^PQR (nowj q)    (nowj p)    = nowj (trans^PQR q p)
 transitive trans^PQR (nown)    (nown)    = nown 
 transitive trans^PQR (later ps) (later qs) =
   later λ where .force → transitive trans^PQR (ps .force) (qs .force)


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

 trans : ∀ {i} → Transitive (i ⊢_≈_)
 trans = transitive Eq.trans

------------------------------------------------------------------------
-- Examples 
module _ {a b c} {A : Set a} {B : Set b} {C : Set c}
         {r} {P : A → B → Set r} {Q : B → C → Set r} {R : A → C → Set r} where
  open import Partial.Base

  fail-refl : ∀ {i} -> i ⊢ (fail {A = A}) ≈ (fail {A = A})
  fail-refl = refl

  never-refl : ∀ {i} -> i ⊢ (never {A = A}) ≈ (never {A = A})
  never-refl = refl
