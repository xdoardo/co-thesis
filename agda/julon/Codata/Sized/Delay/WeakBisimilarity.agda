{-# OPTIONS --allow-unsolved-metas #-} 
------------------------------------------------------------------------
-- Weak bisimilarity for the partiality monad 
------------------------------------------------------------------------

module Codata.Sized.Delay.WeakBisimilarity where 

open import Codata.Sized.Delay.WeakBisimilarity.Core public 
---

module _ {ℓ} {A : Set ℓ} {ℓ'} {B : Set ℓ'} where 
 open import Size
 open import Codata.Sized.Delay
 open import Codata.Sized.Thunk
 open import Relation.Binary.PropositionalEquality
 open import Codata.Sized.Delay.WeakBisimilarity.Relation.Binary.Equivalence 
  using () renaming (refl to prefl)
 
 unroll : ∀ {x : Delay A ∞} {v : A} (h : ∞ ⊢ x ≋ now v) 
  (f : ∀ {v} {y} (h≋ : ∞ ⊢ x ≋ y) (h : y ≡ now v) -> B) -> B
 unroll {.(now v)} {v} (now refl) f = f (now refl) refl
 unroll {.(later _)} {v} (laterₗ {xs} h) f 
  with (force xs) in eq-fx
 ... | now x  
  with h 
 ... | now refl = f (laterₗ k) refl
  where
   k : ∞ ⊢ force xs ≋ now x
   k rewrite eq-fx = now refl
 unroll {.(later _)} {v} (laterₗ {xs} (laterₗ {xs'} h)) f | later x = unroll {force x} {v} h k
  where 
   k' : ∞ ⊢ force xs ≋ later x
   k' rewrite eq-fx = prefl
   k : {v : A} {y : Delay A ∞} → ∞ ⊢ force x ≋ y → y ≡ now v → B
   k {v} {y} h = f (laterₗ ?)

