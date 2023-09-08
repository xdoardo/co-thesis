-- {-# OPTIONS --allow-unsolved-metas #-} 
------------------------------------------------------------------------
-- Weak bisimilarity for the partiality monad 
------------------------------------------------------------------------

module Codata.Sized.Partial.Bisimilarity.Properties where 

open import Size
open import Data.Empty
open import Data.Maybe
open import Codata.Sized.Thunk
open import Codata.Sized.Delay
open import Relation.Binary.PropositionalEquality
open import Codata.Sized.Partial.Bisimilarity.Core
open import Codata.Sized.Partial.Effectful renaming (bind to _>>=ᵖ_)
open import Codata.Sized.Partial.Bisimilarity.Relation.Binary.Equivalence using (≡=>≈)
--- 

module _ {a} {A : Set a} where

-- mutual 
--  bind-≈ : ∀ {x y : Delay (Maybe A) ∞} {f : A -> Delay (Maybe A) ∞} (x≈y : ∞ ⊢ x ≈ y) 
--   -> ∞ ⊢ (x >>=ᵖ f) ≈ (y >>=ᵖ f)
--  bind-≈ {now .nothing} {now .nothing} {f} nown = nown
--  bind-≈ {now .(just _)} {now .(just _)} {f} (nowj {x} {y} x≡y) rewrite x≡y = (≡=>≈ refl) 
--  bind-≈ {now x} {later x₁} {f} (laterᵣ x≈y) 
--   with (force x₁) in eq-f-x
--  ... | now x₂ with x≈y
--  ... | nown rewrite eq-f-x = laterᵣ h
--   where 
--    h : ∞ ⊢ (now nothing) ≈ ((force x₁) >>=ᵖ f)
--    h rewrite eq-f-x = nown
--  ... | nowj {x} {y} eq-x rewrite eq-x = laterᵣ h
--   where 
--    h : ∞ ⊢ (f y) ≈ ((force x₁) >>=ᵖ f)
--    h rewrite eq-f-x = ≡=>≈ refl 
--  bind-≈ {now x} {later x₁} {f} (laterᵣ x≈y) | later x₂ = laterᵣ h
--   where 
--    h : ∞ ⊢ ((now x) >>=ᵖ f) ≈ ((force x₁) >>=ᵖ f)
--    h rewrite eq-f-x = bind-≈ x≈y
--  bind-≈ {later x} {now x₁} {f} x≈y  with (force x) in eq-f-x
--  ... | now x₂ with x≈y
--  ... | laterₗ x≈y rewrite eq-f-x with x≈y
--  ... | nown = laterₗ h 
--   where 
--    h : ∞ ⊢ ((force x) >>=ᵖ f) ≈ ((now nothing) >>=ᵖ f)
--    h rewrite eq-f-x = bind-≈ {f = f} x≈y
--  ... | nowj {x'} {y'} refl = laterₗ h
--   where 
--    h : ∞ ⊢ ((force x) >>=ᵖ f) ≈ ((now (just x')) >>=ᵖ f)
--    h rewrite eq-f-x = bind-≈ {f = f} x≈y
--  bind-≈ {later x} {now x₁} {f} (laterₗ x≈y) | later x₂ = laterₗ h
--   where 
--    h : ∞ ⊢ ((force x) >>=ᵖ f) ≈ ((now x₁) >>=ᵖ f)
--    h rewrite eq-f-x = bind-≈ {f = f} x≈y
--  bind-≈ {later x} {later x₁} {f} (laterₗ x≈y) with (force x) in eq-f-x
--  ... | now x₂ = laterₗ h
--   where 
--    h : ∞ ⊢ ((force x) >>=ᵖ f) ≈ ((later x₁) >>=ᵖ f)
--    h rewrite eq-f-x = bind-≈ x≈y
--  ... | later x₂ = laterₗ h 
--   where 
--    h : ∞ ⊢ ((force x) >>=ᵖ f) ≈ ((later x₁) >>=ᵖ f)
--    h rewrite eq-f-x = bind-≈ x≈y
--  bind-≈ {later x} {later x₁} {f} (laterᵣ x≈y)
--   with (force x₁) in eq-f-x
--  ... | now x₂ = laterᵣ h
--   where 
--    h : ∞ ⊢ ((later x) >>=ᵖ f) ≈ ((force x₁) >>=ᵖ f)
--    h rewrite eq-f-x = bind-≈ x≈y
--  ... | later x₂ = laterᵣ h
--   where 
--    h : ∞ ⊢ ((later x) >>=ᵖ f) ≈ ((force x₁) >>=ᵖ f)
--    h rewrite eq-f-x = bind-≈ x≈y
--  bind-≈ {later x} {later x₁} {f} (later x₂) = later  (∞bind-≈ {x} {x₁} {f} x₂)
--
--  private
--   ∞bind-≈ : ∀ {x y : Thunk (Delay (Maybe A)) ∞} {f : A -> Delay (Maybe A) ∞} (x≈y : Thunk (λ i -> i ⊢ (force x) ≈ force y) ∞) 
--    -> Thunk (λ i -> i ⊢ ((force x) >>=ᵖ f) ≈ ((force y) >>=ᵖ f)) ∞
--   force (∞bind-≈ {x} {y} x≈y) with (force x) | (force y)
--   ... | now x₁ | now x₂ with (force x≈y)
--   ... | nown = nown 
--   ... | nowj refl = (≡=>≈ refl) 
--   force (∞bind-≈ {x} {y} {f} x≈y) {j} | now x₁ | later x₂ with (force x≈y) 
--   ... | laterᵣ x≈y₁ with (force x₂) in eq-f-x₂
--   ... | now x₃ = laterᵣ h 
--    where 
--     h : j ⊢ (now x₁ >>=ᵖ f) ≈ ((force x₂) >>=ᵖ f)
--     h rewrite eq-f-x₂ = bind-≈ x≈y₁ 
--   force (∞bind-≈ {x} {y} {f} x≈y) | now x₁ | later x₂ | laterᵣ x≈y₁ | later x₃ 
--    = {! !}
--   force (∞bind-≈ {x} {y} {f} x≈y) | later x₁ | now x₂ = {! !}
--   force (∞bind-≈ {x} {y} {f} x≈y) | later x₁ | later x₂ = {! !}

