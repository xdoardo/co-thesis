------------------------------------------------------------------------
-- Convergence relations for partial types 
------------------------------------------------------------------------

module Codata.Sized.Partial.Relation.Binary.Convergence where

open import Size
open import Data.Maybe
open import Codata.Sized.Delay
open import Codata.Sized.Thunk
open import Relation.Binary.PropositionalEquality
---

data _⊢_⇓_ {a} {A : Set a} (i : Size) : (Delay (Maybe A) i) -> A -> Set a where 
 now⇓ : ∀ {x : A} -> i ⊢ (now (just x)) ⇓ x
 later⇓ : ∀ {j : Size< i} {x : A} {d : Thunk (Delay (Maybe A)) i} -> j ⊢ (force d) ⇓ x -> i ⊢ later (d) ⇓ x

data _⊢_⇑ {a} {A : Set a} (i : Size) : (Delay (Maybe A) i) -> Set a where 
 later⇑ : ∀ {j : Size< i} {d : Thunk (Delay (Maybe A)) i} -> j ⊢ (force d) ⇑ -> i ⊢ later (d) ⇑ 

data _↯ {a} {A : Set a} : {i : Size} -> (Delay (Maybe A) i)  -> Set a where
 now↯ :  now nothing ↯  
 later↯ : ∀ {d} -> force d ↯ -> later d ↯

≡=>⇓ : ∀ {a} {A : Set a} {i} {v : A} {c x : Delay (Maybe A) i} -> (h : c ≡ x) -> (h⇓ : i ⊢ x ⇓ v) -> i ⊢ c ⇓ v
≡=>⇓ h h⇓ rewrite h = h⇓  
