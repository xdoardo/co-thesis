{-# OPTIONS --allow-unsolved-metas #-}
------------------------------------------------------------------------
-- Properties of functional semantics for Imp
------------------------------------------------------------------------
module Imp.Semantics.BigStep.Functional.Properties where 

open import Size
open import Data.Or
open import Data.Empty
open import Imp.Syntax
open import Data.Maybe
open import Data.Product
open import Data.Irrelevant
open import Codata.Sized.Thunk
open import Codata.Sized.Partial
open import Codata.Sized.Delay hiding (_⇓)
open import Imp.Semantics.BigStep.Functional
open import Codata.Sized.Partial.Bisimilarity
open import Relation.Binary.PropositionalEquality
open import Codata.Sized.Partial.Bisimilarity.Properties
open import Codata.Sized.Partial.Relation.Binary.Convergence 
open import Codata.Sized.Partial.Bisimilarity.Relation.Binary.Equivalence 
 renaming (sym to psym ; refl to prefl ; trans to ptrans)
--

-- @TODO
postulate
 ceval-⇓=>⊆ : ∀ (c : Command) (s s' : Store) -> (h : (ceval c s) ⇓ s') -> dom s ⊆ dom s'
 ceval=>⊆ : ∀ (c : Command) (s s' : Store) -> (h : (ceval c s) ≡  now (just s')) -> dom s ⊆ dom s'
 ⊏ᶜ=>⇑ : ∀ {s s' : Store} {cₛ c : Command} (h-⊆ : dom s ⊆ dom s') -> (h-⊏ : cₛ ⊏ᶜ c) -> 
  (h-⇑ : (ceval cₛ s') ⇑) -> (ceval c s) ⇑
 ⇑->↯=>⊥ : ∀ {c : Command} {s : Store} -> (h⇑ : (ceval c s) ⇑) -> (h↯ : (ceval c s) ↯) -> ⊥

⇓=>≡ : ∀ {a} {A : Set a} (x : Delay (Maybe A) ∞) (y z : A) (h : x ⇓ z) (h₁ : x ≡ (now (just y))) -> (z ≡ y)
⇓=>≡ .(now (just y)) y z (nowj h-≡) refl rewrite h-≡ = refl
