------------------------------------------------------------------------
-- Properties of functional semantics for Imp
------------------------------------------------------------------------
module Imp.Semantics.BigStep.Functional.Properties where 

open import Imp.Syntax
open import Imp.Semantics.BigStep.Functional
open import Codata.Sized.Partial.Relation.Binary.Convergence 
open import Codata.Sized.Partial.Relation.Unary.Convergence 
--

-- @TODO
postulate
 ceval=>⊆ : ∀ (c : Command) (s s' : Store) -> (h : ceval c s ⇓ s') -> dom s ⊆ dom s'
 ⊏ᶜ=>⇑ : ∀ {s s' : Store} (h-⊆ : dom s ⊆ dom s') (cₛ c : Command) -> (h-⊏ : cₛ ⊏ᶜ c) -> (h-⇑ : (ceval cₛ s') ⇑) -> (ceval c s) ⇑
