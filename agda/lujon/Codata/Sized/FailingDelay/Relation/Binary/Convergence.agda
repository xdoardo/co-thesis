------------------------------------------------------------------------
-- Convergence relations for partial types 
------------------------------------------------------------------------

module Codata.Sized.FailingDelay.Relation.Binary.Convergence where

open import Size
open import Data.Or
open import Data.Nat
open import Data.Maybe
open import Data.Product
open import Codata.Sized.Thunk
open import Function using (case_of_)
open import Codata.Sized.FailingDelay.Effectful
open import Codata.Sized.Delay.WeakBisimilarity
open import Codata.Sized.Delay hiding (_⇓ ; bind)
open import Relation.Binary.PropositionalEquality
open import Codata.Sized.Delay.WeakBisimilarity.Relation.Binary.Equivalence using (≡=>≋)
---

module _ {ℓ} {A : Set ℓ} where
 _⇓_ : ∀ (x : Delay (Maybe A) ∞) (v : A) -> Set ℓ
 x ⇓ v = ∞ ⊢ x ≋ (now (just v))

 _⇓ : ∀ (x : Delay (Maybe A) ∞) -> Set ℓ
 x ⇓ = ∃ λ v -> ∞ ⊢ x ≋ (now (just v))

 _↯ : ∀ (x : Delay (Maybe A) ∞) -> Set ℓ 
 x ↯ = ∞ ⊢ x ≋ now nothing

 _⇑ : ∀ (x : Delay (Maybe A) ∞) -> Set ℓ
 x ⇑ = ∞ ⊢ x ≋ never 

 ≡=>⇓ : ∀ {v : A} {c x : Delay (Maybe A) ∞} -> (h : c ≡ x) -> (h⇓ : x ⇓ v) -> c ⇓ v
 ≡=>⇓ h h⇓ rewrite h = h⇓  

 ≡=>↯ : ∀ {v : A} {c x : Delay (Maybe A) ∞} -> (h : c ≡ x) -> (h↯ : x ↯) -> c ↯
 ≡=>↯ h h↯ rewrite h = h↯  

 private
  ∞bindxf⇓=>x⇓ : ∀ {x : Thunk (Delay (Maybe A)) ∞} {f} {v} (h⇓ : (bind (x .force) f) ⇓ v) -> (x .force) ⇓ 
  ∞bindxf⇓=>x⇓ {x} {f} h⇓ with (force x) in eq-force-x
  ... | now (just x₁) = x₁ , now refl
  ∞bindxf⇓=>x⇓ {x} {f} h⇓ | now nothing 
   with h⇓
  ... | now ()
  ∞bindxf⇓=>x⇓ {x} {f} h⇓ | later x₁ with (h⇓) 
  ... | laterₗ h⇓'
   with (∞bindxf⇓=>x⇓ {x₁} {f} h⇓')
  ... | s' , eq-x₁ = s' , laterₗ eq-x₁

 bindxf⇓=>x⇓ : ∀ {x} {f} {v} (h⇓ : (bind x f) ⇓ v) -> x ⇓
 bindxf⇓=>x⇓ {now (just x)} {f} {v} h⇓ = x , now refl
 bindxf⇓=>x⇓ {now nothing} {f} {v} h⇓ = v , h⇓
 bindxf⇓=>x⇓ {later x} {f} {v} h⇓ with h⇓
 ... | laterₗ h⇓' with (force x) in eq-force-x
 ... | now (just x₁) = x₁ , laterₗ (≡=>≋ eq-force-x)
 ... | now nothing 
  with h⇓'
 ... | now ()
 bindxf⇓=>x⇓ {later x} {f} h⇓ | laterₗ (laterₗ h⇓') | later x₁ 
  with (∞bindxf⇓=>x⇓ {x₁} {f} h⇓') 
 ... | s' , eq-x₁ = s' , laterₗ h 
  where 
   h : (force x) ⇓ s'
   h rewrite eq-force-x = laterₗ eq-x₁

 bindxf⇓-x⇓=>f⇓ : ∀ {x} {f} {v v'} (h⇓ : (bind x f) ⇓ v) (hx⇓ : x ⇓ v') -> f v' ⇓ v
 bindxf⇓-x⇓=>f⇓ {now (just x)} {f} {v} {.x} h⇓ (now refl) = h⇓
 bindxf⇓-x⇓=>f⇓ {later x} {f} {v} {v'} h⇓ (laterₗ {xs} hx⇓)
  with (force xs) in eq-fx
 ... | now (just x₁)
  with hx⇓
 ... | now refl
  with h⇓
 ... | laterₗ n rewrite eq-fx = n
 bindxf⇓-x⇓=>f⇓ {later x} {f} {v} {v'} h⇓ (laterₗ {x} (now ())) | now nothing
 bindxf⇓-x⇓=>f⇓ {later x} {f} {v} {v'} (laterₗ h⇓) (laterₗ {xs} hx⇓) | later x₁ 
  rewrite eq-fx
  =  bindxf⇓-x⇓=>f⇓ {later x₁} h⇓ hx⇓

postulate 
 three-states : ∀ {a} {A : Set a} {x : Delay (Maybe A) ∞} -> XOr (x ⇓) (XOr (x ⇑) (x ↯))
