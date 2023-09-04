{-# OPTIONS --allow-unsolved-metas #-} 
------------------------------------------------------------------------
-- Properties of functional semantics for Imp
------------------------------------------------------------------------
module Imp.Semantics.BigStep.Functional.Properties where 

open import Size
open import Data.Or
open import Data.Empty
open import Imp.Syntax
open import Data.Bool
open import Data.Maybe
open import Data.Product
open import Data.Irrelevant
open import Codata.Sized.Thunk
open import Codata.Sized.Partial
open import Codata.Sized.Delay hiding (_⇓)
open import Imp.Semantics.BigStep.Functional
open import Codata.Sized.Partial.Bisimilarity
open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Codata.Sized.Partial.Bisimilarity.Properties
open import Codata.Sized.Partial.Relation.Binary.Convergence 
open import Codata.Sized.Partial.Bisimilarity.Relation.Binary.Equivalence 
 renaming (sym to psym ; refl to prefl ; trans to ptrans)
--


private
 cvars-skip : (cvars skip) ≡ ∅ 
 cvars-skip = refl

ceval=>cvars : ∀ (c : Command) (s s' : Store) -> (h : (ceval c s) ≡  now (just s')) -> dom s' ≡  (dom s ∪ (cvars c))
ceval=>cvars skip s .s refl rewrite cvars-skip rewrite (∪-∅  {dom s}) = refl  
ceval=>cvars (assign id a) s s' h  = ? 
ceval=>cvars (seq c₁ c₂) s sᶠ h with (ceval c₁ s) in eq-ceval-c₁
... | now (just s') with (ceval=>cvars c₁ s s' eq-ceval-c₁) 
... | c₁-cv with (ceval c₂ s') in eq-ceval-c₂
... | now (just x) with h
... | refl with (ceval=>cvars c₂ s' sᶠ eq-ceval-c₂) 
... | c₂-cv = if-ext λ { x₁ → {! !} }
ceval=>cvars (ifelse b c c₁) s s' h = {! !}
ceval=>cvars (while b c) s s' h = {! !}

ceval=>⊆ : ∀ (c : Command) (s s' : Store) -> (h : (ceval c s) ≡  now (just s')) -> dom s ⊆ dom s'
ceval=>⊆ c s s' h x x-in-s = in-⊆ {dom s} {cvars c} x-in-s (ceval=>cvars c s s' h)

ceval-⇓=>⊆ : ∀ (c : Command) (s s' : Store) -> (h : (ceval c s) ⇓ s') -> dom s ⊆ dom s'
ceval-⇓=>⊆ c s s' h with (ceval c s) in eq-ceval 
... | now (just x₁) with h
... | nowj r rewrite r = ceval=>⊆ c s s' eq-ceval
ceval-⇓=>⊆ c s s' h | later x₁ = ? 

⇓=>≡ : ∀ {a} {A : Set a} (x : Delay (Maybe A) ∞) (y z : A) (h : x ⇓ z) (h₁ : x ≡ (now (just y))) -> (z ≡ y)
⇓=>≡ .(now (just y)) y z (nowj h-≡) refl rewrite h-≡ = refl
