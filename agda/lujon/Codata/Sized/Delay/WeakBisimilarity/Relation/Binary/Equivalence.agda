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

 transitive-now : ∀ {i} {x y z} (t : Trans P Q R) (p : WeakBisim P ∞ (now x) y) 
  (q : WeakBisim Q ∞ y z) -> WeakBisim R i (now x) z
 transitive-now t (now p) (now q) = now (t p q)
 transitive-now t (now p) (laterᵣ q) = laterᵣ (transitive-now t (now p) q) 
 transitive-now t (laterᵣ p) (later x) = laterᵣ (transitive-now t p (force x))
 transitive-now t (laterᵣ p) (laterᵣ q) = laterᵣ (transitive-now t p (laterˡ⁻¹ q))
 transitive-now t (laterᵣ p) (laterₗ q) = transitive-now t p q
 
 mutual 
  transitive-later : ∀ {i} {x y z} (t : Trans P Q R) (p : WeakBisim P ∞ (later x) y) 
   (q : WeakBisim Q ∞ y z) -> WeakBisim R i (later x) z
  transitive-later t p (later q)  = later λ { .force → transitive t (later⁻¹ p) (force q) }
  transitive-later t p (laterᵣ q) = later λ { .force → transitive t (laterˡ⁻¹ p) q }
  transitive-later t p (laterₗ q) = transitive-later t (laterʳ⁻¹ p) q
  transitive-later t (laterₗ p) (now q) = laterₗ (transitive t p (now q))

  transitive : ∀ {i} (t : Trans P Q R) -> Trans (WeakBisim P ∞) (WeakBisim Q ∞) (WeakBisim R i)
  transitive t {now x} p q = transitive-now t p q 
  transitive t {later x} p q = transitive-later t p q 


module _ {a} {A : Set a} where


 -- Pointwise Equality as a Bisimilarity
 refl : ∀ {i} -> Reflexive {a} {Delay A ∞} (i ⊢_≋_)
 refl = reflexive Eq.refl
 
 sym : ∀ {i} -> Symmetric {a} {Delay A ∞}(i ⊢_≋_)
 sym = symmetric Eq.sym
 
 trans : Transitive {a} {Delay A ∞} (∞ ⊢_≋_)
 trans = transitive Eq.trans

 ≡=>≋ : ∀ {a₁ a₂ : Delay A ∞} -> (h : a₁ ≡ a₂) -> (∀ {i} -> i ⊢ a₁ ≋ a₂)
 ≡=>≋ {a₁} {.a₁} Eq.refl {i} = refl
