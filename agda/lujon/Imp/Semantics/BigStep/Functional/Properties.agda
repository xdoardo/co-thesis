------------------------------------------------------------------------
-- Properties of functional semantics for Imp
------------------------------------------------------------------------
module Imp.Semantics.BigStep.Functional.Properties where 

open import Size
open import Data.Empty
open import Imp.Syntax
open import Data.Maybe
open import Data.Product
open import Data.Irrelevant
open import Codata.Sized.Delay
open import Codata.Sized.Partial
open import Imp.Semantics.BigStep.Functional
open import Codata.Sized.Partial.Bisimilarity
open import Relation.Binary.PropositionalEquality
open import Codata.Sized.Partial.Bisimilarity.Properties
open import Codata.Sized.Partial.Relation.Unary.Convergence 
open import Codata.Sized.Partial.Relation.Binary.Convergence 
--

-- @TODO
postulate
 ceval=>⊆ : ∀ {i} (c : Command) (s s' : Store) -> (h : i ⊢ (ceval {i} c s) ⇓ s') -> dom s ⊆ dom s'
 ⊏ᶜ=>⇑ : ∀ {s s' : Store} {i} (h-⊆ : dom s ⊆ dom s') (cₛ c : Command) -> (h-⊏ : cₛ ⊏ᶜ c) 
  -> (h-⇑ : i ⊢ (ceval cₛ s') ⇑) -> i ⊢ (ceval c s) ⇑
 

⇓=>≡ : ∀ {a} {A : Set a} {i} (x : Delay (Maybe A) i) (y z : A) (h : i ⊢ x ⇓ z) (h₁ : x ≡ (now (just y))) -> (z ≡ y)
⇓=>≡ (now (just x)) .x .x now⇓ refl = refl
