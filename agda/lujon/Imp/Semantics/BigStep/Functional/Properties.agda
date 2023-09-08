{-# OPTIONS --allow-unsolved-metas #-} 
------------------------------------------------------------------------
-- Properties of functional semantics for Imp
------------------------------------------------------------------------
module Imp.Semantics.BigStep.Functional.Properties where 

open import Size
open import Data.Or
open import Function using (case_of_)
open import Data.Bool
open import Data.Maybe
open import Data.Empty
open import Imp.Syntax
open import Data.Product
open import Data.Integer
open import Data.Irrelevant
open import Codata.Sized.Thunk
open import Codata.Sized.Partial
open import Data.Bool.Properties
open import Codata.Sized.Delay hiding (_⇓)
open import Imp.Semantics.BigStep.Functional
open import Codata.Sized.Partial.Bisimilarity
open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Codata.Sized.Partial.Effectful using () renaming (bind to bindᵖ)
open import Codata.Sized.Partial.Bisimilarity.Properties
open import Codata.Sized.Partial.Relation.Binary.Convergence 
open import Data.String using (String ; _==_) renaming (_≟_ to _≟ₛ_)
open import Codata.Sized.Partial.Bisimilarity.Relation.Binary.Equivalence 
 renaming (sym to psym ; refl to prefl ; trans to ptrans)
--

⇓=>≡ : ∀ {a} {A : Set a} (x : Delay (Maybe A) ∞) (y z : A) (h : x ⇓ z) (h₁ : x ≡ (now (just y))) -> (z ≡ y)
⇓=>≡ .(now (just y)) y z (nowj h-≡) refl rewrite h-≡ = refl

ceval-now=>⊆ : ∀ (c : Command) (s s' : Store) -> (h-n : (ceval c s) ≡ now (just s')) -> dom s ⊆ dom s'
ceval-now=>⊆ skip s .s refl id id∈s = id∈s
ceval-now=>⊆ (assign id₁ a) s s' h-n id id∈s 
 with (aeval a s) 
... | just v with h-n
... | refl with (id₁ == id) in eq-id 
... | true = refl 
... | false rewrite (==-refl {id}) rewrite eq-id rewrite id∈s = id∈s
ceval-now=>⊆ (ifelse b cᵗ cᶠ) s s' h-n id id∈s 
 with (beval b s) in eq-beval-b
... | just true rewrite eq-beval-b = ceval-now=>⊆ cᵗ s s' h-n id id∈s
... | just false rewrite eq-beval-b = ceval-now=>⊆ cᶠ s s' h-n id id∈s
ceval-now=>⊆ (seq c₁ c₂) s s' h-n id id∈s 
 with (ceval c₁ s) in eq-ceval-c₁
... | now (just sⁱ) 
 with (ceval-now=>⊆ c₁ s sⁱ eq-ceval-c₁ id id∈s)
... | id∈sⁱ = ceval-now=>⊆ c₂ sⁱ s' h-n id id∈sⁱ
ceval-now=>⊆ (while b c) s s' h-n id id∈s 
 with (beval b s) in eq-beval-b
... | just false rewrite eq-beval-b with h-n
... | refl = id∈s
ceval-now=>⊆ (while b c) s s' h-n id id∈s 
 | just true rewrite eq-beval-b
 with (ceval c s) in eq-ceval-c
... | now nothing rewrite eq-ceval-c = case h-n of λ () 
... | now (just sⁱ) rewrite eq-ceval-c with h-n
... | ()

ceval-later=>⊆ : ∀ {x x' : Thunk (Delay (Maybe Store)) ∞} (c : Command) (s s' : Store) 
 (h-n : (ceval c s) ≡ later x) (h-≈ : ∞ ⊢  later x ≈ force x') -> (h⇓ : force x' ⇓ s') -> dom s ⊆ dom s'
ceval-later=>⊆ {x} {x'} (ifelse b cᵗ cᶠ) s s' h-n h-≈ h⇓
 with (beval b s) in eq-beval-b
... | just false rewrite eq-beval-b = ceval-later=>⊆ {x' = record { force = force x' }} cᶠ s s' h-n h-≈ h⇓ 
... | just true rewrite eq-beval-b = ceval-later=>⊆ {x' = record { force = force x' }} cᵗ s s' h-n h-≈ h⇓ 
ceval-later=>⊆ {x} {x'} (seq c₁ c₂) s s' h-n h-≈ h⇓ id id∈s
 with (ceval c₁ s) in eq-ceval-c
... | now (just sⁱ) 
 with (ceval-now=>⊆ c₁ s sⁱ eq-ceval-c id id∈s)
... | id∈sⁱ with (ceval c₂ sⁱ) in eq-ceval-c₂
... | later tc₂ rewrite eq-ceval-c₂ with h-n
... | refl = ceval-later=>⊆ {x' = record { force = force x' }} c₂ sⁱ s' eq-ceval-c₂ h-≈ h⇓ id id∈sⁱ
ceval-later=>⊆ (seq c₁ c₂) s s' h-n h-≈ h⇓ id id∈s
 | later x = {! !}
ceval-later=>⊆ (while b c) s s' h-n h-≈ h⇓ id id∈s
 with (beval b s) in eq-beval-b
... | just true rewrite eq-beval-b 
 with (ceval c s) in eq-ceval-c
... | now (just sⁱ) with (ceval-now=>⊆ c s sⁱ eq-ceval-c id id∈s) 
... | id∈sⁱ = ?
-- = ceval-later=>⊆ (while b c) sⁱ s' ? ? ? id id∈sⁱ
ceval-later=>⊆ (while b c) s s' h-n h-≈ h⇓ id id∈s | just true | later x = {! !}

--ceval⇓=>⊆ : ∀ (c : Command) (s s' : Store) -> (h : (ceval c s) ⇓ s') -> dom s ⊆ dom s'
--ceval⇓=>⊆ c s s' h 
-- with (ceval c s) in eq-ceval-c
--... | later x = ceval-later=>⊆ c s s' eq-ceval-c h
--... | now (just x) with h
--... | nowj refl = ceval-now=>⊆ c s x eq-ceval-c 

--mutual 
-- ceval⇓=>⊆ : ∀ (c : Command) (s s' : Store) -> (h : (ceval c s) ⇓ s') -> dom s ⊆ dom s'
-- ceval⇓=>⊆ skip s .s (nowj refl) x x∈s = x∈s
-- ceval⇓=>⊆ (assign id a) s s' h x x∈s with (aeval a s) 
-- ... | just v  with h
-- ... | nowj refl with (id == x) in eq-id
-- ... | true = refl
-- ... | false rewrite (==-refl {id}) rewrite eq-id rewrite x∈s = x∈s
-- ceval⇓=>⊆ (ifelse b cᵗ cᶠ) s s' h x x∈s 
--  with (beval b s) in eq-beval-b
-- ... | just true rewrite eq-beval-b = ceval⇓=>⊆ cᵗ s s' h x x∈s
-- ... | just false rewrite eq-beval-b = ceval⇓=>⊆ cᶠ s s' h x x∈s
-- ceval⇓=>⊆ (seq c₁ c₂) s s' h x x∈s 
--  with (ceval c₁ s) in eq-ceval-c₁
-- ... | now (just sⁱ)  
--  rewrite eq-ceval-c₁ 
--  = (⊆-trans (ceval⇓=>⊆ c₁ s sⁱ (≡=>≈ eq-ceval-c₁)) (ceval⇓=>⊆ c₂ sⁱ s' h)) x x∈s
-- ceval⇓=>⊆ (seq c₁ c₂) s s' h x x∈s | later x₁ 
--  with h
-- ... | laterₗ fx⇓ with (force x₁) in eq-fx
-- ... | now (just sⁱ) 
--  rewrite eq-fx 
--  = (⊆-trans (ceval⇓=>⊆ c₁ s sⁱ h') (ceval⇓=>⊆ c₂ sⁱ s' fx⇓)) x x∈s
--  where 
--   h' : ∞ ⊢ (ceval c₁ s) ≈ (now (just sⁱ))
--   h' rewrite eq-ceval-c₁ = laterₗ (≡=>≈ eq-fx) 
-- ceval⇓=>⊆ (seq c₁ c₂) s s' h x x∈s | later x₁ | laterₗ fx⇓ | later x₂ = {! !}
-- ceval⇓=>⊆ (while b c) s s' h x x∈s 
--  with (beval b s) in eq-beval-b
-- ... | just false 
--  rewrite eq-beval-b 
--  with h
-- ... | nowj refl = x∈s
-- ceval⇓=>⊆ (while b c) s s' h x x∈s | just true 
--  rewrite eq-beval-b 
--  with (ceval c s) in eq-ceval-c 
-- ... | now (just sⁱ)
--  with (dom sⁱ x) in x∈sⁱ
-- ... | false with (ceval⇓=>⊆ c s sⁱ (≡=>≈ eq-ceval-c) x x∈s)
-- ... | n rewrite x∈sⁱ with n
-- ... | ()
-- ceval⇓=>⊆ (while b c) s s' h x x∈s | just true | now (just sⁱ) | true with h
-- ... | laterₗ w⇓ with (ceval (while b c) sⁱ) in eq-ceval-w
-- ... | now (just s') with w⇓
-- ... | nowj refl with (dom s' x)
-- ... | true = refl
-- ... | false with (ceval⇓=>⊆ (while b c) sⁱ s' (≡=>≈ eq-ceval-w) x x∈sⁱ) 
-- ... | n = ?
-- ceval⇓=>⊆ (while b c) s s' h x x∈s | just true | now (just sⁱ) | true | laterₗ w⇓ | later x₁ = {! !}
-- ceval⇓=>⊆ (while b c) s s' h x x∈s | just true | later x₁ = {! !}


ceval⇓=>sc⊆s' :  ∀ (c : Command) (s s' : Store) -> (h⇓  : (ceval c s) ⇓ s') -> (dom s ∪ (cvars c)) ⊆ (dom s')
ceval⇓=>sc⊆s' = ?
