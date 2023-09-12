{-# OPTIONS --allow-unsolved-metas #-}
------------------------------------------------------------------------
-- Convergence relations for partial types 
------------------------------------------------------------------------

module Codata.Sized.Partial.Relation.Binary.Convergence where

open import Size
open import Data.Nat
open import Data.Maybe
open import Data.Product
open import Codata.Sized.Thunk
open import Codata.Sized.Partial.Effectful
open import Codata.Sized.Partial.Bisimilarity
open import Codata.Sized.Delay hiding (_⇓ ; bind)
open import Relation.Binary.PropositionalEquality
open import Codata.Sized.Partial.Bisimilarity.Relation.Binary.Equivalence 
 renaming (sym to psym ; refl to prefl ; trans to ptrans)
---

module _ {ℓ} {A : Set ℓ} where
 _⇓_ : ∀ (x : Delay (Maybe A) ∞) (v : A) -> Set ℓ
 x ⇓ v = ∞ ⊢ x ≈ (now (just v))

 _⇓ : ∀ (x : Delay (Maybe A) ∞) -> Set ℓ
 x ⇓ = ∃ λ v -> ∞ ⊢ x ≈ (now (just v))

 _↯ : ∀ (x : Delay (Maybe A) ∞) -> Set ℓ 
 x ↯ = ∞ ⊢ x ≈ now nothing

 _⇑ : ∀ (x : Delay (Maybe A) ∞) -> Set ℓ
 x ⇑ = ∞ ⊢ x ≈ never 

 ≡=>⇓ : ∀ {v : A} {c x : Delay (Maybe A) ∞} -> (h : c ≡ x) -> (h⇓ : x ⇓ v) -> c ⇓ v
 ≡=>⇓ h h⇓ rewrite h = h⇓  

 ≡=>↯ : ∀ {v : A} {c x : Delay (Maybe A) ∞} -> (h : c ≡ x) -> (h↯ : x ↯) -> c ↯
 ≡=>↯ h h↯ rewrite h = h↯  

 private
  ∞bindxf⇓=>x⇓ : ∀ {x : Thunk (Delay (Maybe A)) ∞} {f} {v} (h⇓ : (bind (x .force) f) ⇓ v) -> (x .force) ⇓ 
  ∞bindxf⇓=>x⇓ {x} {f} h⇓ with (force x) in eq-force-x
  ... | now (just x₁) = x₁ , nowj refl
  ... | later x₁ with (h⇓) 
  ... | laterₗ h⇓'
   with (∞bindxf⇓=>x⇓ {x₁} {f} h⇓')
  ... | s' , eq-x₁ = s' , laterₗ eq-x₁

 -- TODO
 x⇓-f⇓=>bindxf⇓ : ∀ {x} {f} {v v'} (x⇓ : x ⇓ v) (fv⇓ : f v ⇓ v') -> (bind x f) ⇓ v'
 x⇓-f⇓=>bindxf⇓ = ?

 bindxf⇓=>x⇓ : ∀ {x} {f} {v} (h⇓ : (bind x f) ⇓ v) -> x ⇓
 bindxf⇓=>x⇓ {now (just x)} {f} h⇓ = x , nowj refl 
 bindxf⇓=>x⇓ {later x} {f} h⇓ with h⇓
 ... | laterₗ h⇓' with (force x) in eq-force-x
 ... | now (just x₁) = x₁ , laterₗ (≡=>≈ eq-force-x)
 bindxf⇓=>x⇓ {later x} {f} h⇓ | laterₗ (laterₗ h⇓') | later x₁ 
  with (∞bindxf⇓=>x⇓ {x₁} {f} h⇓') 
 ... | s' , eq-x₁ = s' , laterₗ h 
  where 
   h : (force x) ⇓ s'
   h rewrite eq-force-x = laterₗ eq-x₁

 bindxf⇓-x⇓=>f⇓ : ∀ {x} {f} {v v'} (h⇓ : (bind x f) ⇓ v) (hx⇓ : x ⇓ v') -> f v' ⇓ v
 bindxf⇓-x⇓=>f⇓ {.(now (just _))} {f} {v} {v'} h⇓ (nowj x) rewrite x = h⇓
 bindxf⇓-x⇓=>f⇓ {.(later _)} {f} {v} {v'} h⇓ (laterₗ {xs} hx⇓)  
  with (force xs) in eq-force-xs
 ... | now (just x) with hx⇓
 ... | nowj refl with h⇓
 ... | laterₗ n rewrite eq-force-xs = n
 bindxf⇓-x⇓=>f⇓ {.(later _)} {f} {v} {v'} (laterₗ h⇓) (laterₗ hx⇓) | later x 
  rewrite eq-force-xs
  =  bindxf⇓-x⇓=>f⇓ {later x} h⇓ hx⇓

 bind-↯ : ∀ {x} {f} {v : A} (h⇓ : x ⇓ v) (h↯ : (bind x f) ↯) -> (f v) ↯
 bind-↯ {x} {f} {v} (nowj x≡v) h↯ rewrite x≡v = h↯
 bind-↯ {x} {f} {v} (laterₗ {xs} h⇓) h↯ 
  with (force xs) in eq-force-x
 ... | n 
  with h↯
 ... | laterₗ h↯' = bind-↯ {force xs} {f = f} {v = v} (≡=>⇓ eq-force-x h⇓) h↯' 
 
 ↯-bind : ∀ {x} {f} (x↯ : x ↯) -> (bind x f) ↯
 ↯-bind {.(now nothing)} {f} nown = nown
 ↯-bind {.(later xs)} {f} (laterₗ {xs} x↯) 
  with (force xs) in eq-force-x
 ... | n rewrite (sym eq-force-x) = laterₗ (↯-bind x↯)

 ⇓length : ∀ {x} {v} (h⇓ : x ⇓ v) -> ℕ 
 ⇓length (nowj x) = zero
 ⇓length (laterₗ h⇓) = suc (⇓length h⇓)
