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

module _ {a} {A : Set a} where

 -- Pointwise Equality as a Bisimilarity
 refl : ∀ {i} -> Reflexive {a} {Delay (Maybe A) ∞} (i ⊢_≈_)
 refl = reflexive Eq.refl
 
 sym : ∀ {i} -> Symmetric {a} {Delay (Maybe A) ∞}(i ⊢_≈_)
 sym = symmetric Eq.sym

 ≡=>≈ : ∀ {a₁ a₂ : Delay (Maybe A) ∞} -> (h : a₁ ≡ a₂) -> (∀ {i} -> i ⊢ a₁ ≈ a₂)
 ≡=>≈ {a₁} {.a₁} Eq.refl {i} = refl
