------------------------------------------------------------------------
-- Weak bisimilarity for the partiality monad 
------------------------------------------------------------------------
module Codata.Sized.Partial.Bisimilarity.Relation.Binary.Equivalence where

open import Size
open import Level
open import Data.Maybe
open import Relation.Binary
open import Codata.Sized.Thunk
open import Codata.Sized.Delay hiding (never ; _⇓)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Codata.Sized.Partial.Bisimilarity.Core
--- 


module _ {a r} {A : Set a} {R : A -> A -> Set r} where
 
 reflexive : Reflexive R -> ∀ {i} -> Reflexive (Bisim R i)
 reflexive refl^R {i} {now (just x)} = nowj refl^R
 reflexive refl^R {i} {now nothing} = nown 
 reflexive refl^R {i} {later x} = later λ where .force -> reflexive (refl^R) 
 
module _ {a b} {A : Set a} {B : Set b}
          {r} {P : A -> B -> Set r} {Q : B -> A -> Set r} where
 
 symmetric : Sym P Q -> ∀ {i} -> Sym (Bisim P i) (Bisim Q i)
 symmetric sym^PQ nown = nown 
 symmetric sym^PQ (nowj x) = nowj (sym^PQ x)
 symmetric sym^PQ (later x) = later λ where .force -> symmetric (sym^PQ) (force x)
 symmetric sym^PQ {i} (laterₗ x ) = laterᵣ (symmetric sym^PQ x)
 symmetric sym^PQ (laterᵣ x) = laterₗ (symmetric sym^PQ x)
 

-- @TODO here: prove transitivity of weak bisimilarity...

module _ {a b c} {A : Set a} {B : Set b} {C : Set c}
         {r} {P : A → B → Set r} {Q : B → C → Set r} {R : A → C → Set r} where

 postulate
  transitive : (trel : Trans P Q R) → ∀ {i} → Trans (Bisim P i) (Bisim Q i) (Bisim R i)
-- transitive trel {i} {.(now nothing)} {.(now nothing)} {.(now nothing)} nown nown = nown
-- transitive trel {i} {.(now nothing)} {.(now nothing)} {.(later _)} nown (laterᵣ .{now nothing} {ys} y≈z) 
--  = laterᵣ (transitive trel nown y≈z) 
-- transitive trel {i} {.(now (just _))} {.(now (just _))} {.(now (just _))} (nowj x) (nowj x₁) 
--  = nowj (trel x x₁)
-- transitive trel {i} {.(now (just _))} {.(now (just _))} {.(later _)} (nowj x) (laterᵣ .{now (just _)} {ys} y≈z) 
--  = laterᵣ (transitive trel (nowj x) y≈z) 
-- transitive trel {i} {.(later _)} {.(now nothing)} {.(now nothing)} (laterₗ {xs} x≈y) nown 
--  = laterₗ (transitive trel x≈y nown) 
-- transitive trel {i} {.(later _)} {.(later _)} {.(later _)} (later {xs} x) (later x₁) = ?
-- transitive trel {i} {.(later _)} {.(now (just _))} {.(now (just _))} (laterₗ x≈y) (nowj x) 
--  = laterₗ (transitive trel x≈y (nowj x))
-- transitive trel {i} {.(later _)} {.(later _)} {z} (later x) (laterₗ y≈z) = {! !}
-- transitive trel {i} {.(later _)} {.(later _)} {.(later _)} (later x) (laterᵣ y≈z) = {! !}
-- transitive trel {i} {.(later _)} {.(later _)} {.(later _)} (laterₗ x≈y) (later x) = {! !}
-- transitive trel {i} {.(later _)} {.(later _)} {z} (laterₗ x≈y) (laterₗ y≈z) = {! !}
-- transitive trel {i} {.(later _)} {y} {.(later _)} (laterₗ x≈y) (laterᵣ y≈z) = {! !}
-- transitive trel {i} {x} {.(later _)} {.(later _)} (laterᵣ x≈y) (later x₁) = {! !}
-- transitive trel {i} {x} {.(later _)} {z} (laterᵣ x≈y) (laterₗ y≈z) = {! !}
-- transitive trel {i} {x} {.(later _)} {.(later _)} (laterᵣ x≈y) (laterᵣ y≈z) = {! !}

module _ {a} {A : Set a} where

 -- Pointwise Equality as a Bisimilarity
 refl : ∀ {i} -> Reflexive {a} {Delay (Maybe A) ∞} (i ⊢_≈_)
 refl = reflexive Eq.refl
 
 sym : ∀ {i} -> Symmetric {a} {Delay (Maybe A) ∞}(i ⊢_≈_)
 sym = symmetric Eq.sym
 
 trans : ∀ {i} -> Transitive {a} {Delay (Maybe A) ∞}(i ⊢_≈_)
 trans = transitive Eq.trans

 ≡=>≈ : ∀ {a₁ a₂ : Delay (Maybe A) ∞} -> (h : a₁ ≡ a₂) -> (∀ {i} -> i ⊢ a₁ ≈ a₂)
 ≡=>≈ {a₁} {.a₁} Eq.refl {i} = refl
