------------------------------------------------------------------------
-- Weak bisimilarity is an equivalence relation 
------------------------------------------------------------------------
module Codata.Sized.Delay.WeakBisimilarity.Relation.Binary.Equivalence where

open import Size
open import Level
open import Data.Maybe
open import Relation.Binary
open import Codata.Sized.Thunk
open import Codata.Sized.Delay hiding (never ; _⇓)
open import Codata.Sized.Delay.WeakBisimilarity.Core
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
--- 


module _ {a r} {A : Set a} {R : A -> A -> Set r} where
 
 reflexive : Reflexive R -> ∀ {i} -> Reflexive (WeakBisim R i)
 reflexive refl^R {i} {now x} = now refl^R
 reflexive refl^R {i} {later x} = later λ where .force -> reflexive (refl^R) 
 
module _ {a b} {A : Set a} {B : Set b}
          {r} {P : A -> B -> Set r} {Q : B -> A -> Set r} where
 
 symmetric : Sym P Q -> ∀ {i} -> Sym (WeakBisim P i) (WeakBisim Q i)
 symmetric sym^PQ (now x) = now (sym^PQ x)
 symmetric sym^PQ (later x) = later λ where .force -> symmetric (sym^PQ) (force x)
 symmetric sym^PQ {i} (laterₗ x ) = laterᵣ (symmetric sym^PQ x)
 symmetric sym^PQ (laterᵣ x) = laterₗ (symmetric sym^PQ x)
 

-- @TODO here: prove transitivity of weak bisimilarity...

module _ {a b c} {A : Set a} {B : Set b} {C : Set c}
         {r} {P : A → B → Set r} {Q : B → C → Set r} {R : A → C → Set r} where

 postulate
  transitive : (trel : Trans P Q R) → ∀ {i} → Trans (WeakBisim P i) (WeakBisim Q i) (WeakBisim R i)

module _ {a} {A : Set a} where

 -- Pointwise Equality as a Bisimilarity
 refl : ∀ {i} -> Reflexive {a} {Delay A ∞} (i ⊢_≋_)
 refl = reflexive Eq.refl
 
 sym : ∀ {i} -> Symmetric {a} {Delay A ∞}(i ⊢_≋_)
 sym = symmetric Eq.sym
 
 trans : ∀ {i} -> Transitive {a} {Delay A ∞}(i ⊢_≋_)
 trans = transitive Eq.trans

 ≡=>≋ : ∀ {a₁ a₂ : Delay A ∞} -> (h : a₁ ≡ a₂) -> (∀ {i} -> i ⊢ a₁ ≋ a₂)
 ≡=>≋ {a₁} {.a₁} Eq.refl {i} = refl
