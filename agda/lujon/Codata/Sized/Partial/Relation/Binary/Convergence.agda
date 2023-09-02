------------------------------------------------------------------------
-- Convergence relations for partial types 
------------------------------------------------------------------------

module Codata.Sized.Partial.Relation.Binary.Convergence where

open import Size
open import Data.Maybe
open import Data.Product
open import Codata.Sized.Thunk
open import Codata.Sized.Delay hiding (_⇓ ; bind)
open import Codata.Sized.Partial.Bisimilarity
open import Codata.Sized.Partial.Effectful
open import Relation.Binary.PropositionalEquality
---

--data _⇓_ {a} {A : Set a} : {i : Size} -> (Delay (Maybe A) i) -> A -> Set a where 
-- now⇓ : ∀ {i} {x : A} -> _⇓_ {i = i} (now (just x)) x
-- later⇓ : ∀ {i} {j : Size< i} {x} {d : Thunk (Delay (Maybe A)) i} -> _⇓_ {i = j} (force d) x -> _⇓_ {i = i} (later d) x
--
--_⇓ : ∀ {a} {A : Set a} {i : Size} (x : Delay (Maybe A) i) -> Set a 
--_⇓ {a} {A} {i} x = ∃ λ v -> x ⇓ v 
--
--data _⇑ {a} {A : Set a} : {i : Size} -> (Delay (Maybe A) i) -> Set a where 
-- later⇑ : ∀ {i} {j : Size< i} {d : Thunk (Delay (Maybe A)) i} -> _⇑ {i = j} (force d) -> _⇑ {i = i} (later d)
--
--data _↯ {a} {A : Set a} : {i : Size} -> (Delay (Maybe A) i)  -> Set a where
-- now↯ :  ∀ {i} -> _↯ {i = i} (now nothing)
-- later↯ : ∀ {i} {j : Size< i} {d : Thunk (Delay (Maybe A)) i} -> _↯  (force d) ->  _↯ {i = i} (later d)
--
--≡=>⇓ : ∀ {a} {A : Set a} {i} {v : A} {c x : Delay (Maybe A) i} -> (h : c ≡ x) -> (h⇓ : _⇓_ {i = i} x v) -> _⇓_ {i = i} c v
--≡=>⇓ h h⇓ rewrite h = h⇓  
--
--≡=>↯ : ∀ {a} {A : Set a} {i} {v : A} {c x : Delay (Maybe A) i} -> (h : c ≡ x) -> (h↯ : _↯ {i = i} x) -> _↯ {i = i} c
--≡=>↯ h h↯ rewrite h = h↯  


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
