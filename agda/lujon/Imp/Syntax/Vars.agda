------------------------------------------------------------------------
-- Free variables of terms of Imp
------------------------------------------------------------------------
module Imp.Syntax.Vars where 

open import Data.Bool
open import Data.Maybe
open import Imp.Syntax.Core
open import Imp.Syntax.Ident
open import Data.String using (_==_ ; String)
open import Relation.Binary.PropositionalEquality
open import Axiom.Extensionality.Propositional
open import Data.IndicatorFunction (String) (_==_) renaming (IndicatorFunction to VarsSet) public
---

avars : (a : AExp) -> VarsSet
avars (const n) = ∅ 
avars (var id) = id ↦ ∅
avars (plus a₁ a₂) = (avars a₁) ∪ (avars a₂)

bvars : (b : BExp) -> VarsSet
bvars (const b) = ∅
bvars (le a₁ a₂) = (avars a₁) ∪ (avars a₂)
bvars (not b) = bvars b 
bvars (and b b₁) = (bvars b) ∪ (bvars b₁)

cvars : (c : Command) -> VarsSet
cvars skip = ∅
cvars (assign id a) = id ↦ ∅
cvars (seq c c₁) = (cvars c) ∪ (cvars c₁)
cvars (ifelse b c c₁) = (cvars c) ∪ (cvars c₁)
cvars (while b c) = cvars c

-- A function to build a VarsSet from a Store. 
dom : Store -> VarsSet
dom s x with (s x) 
... | just _ = true 
... | nothing = false 

------------------------------------------------------------------------
-- Properties of variables of Imp 
------------------------------------------------------------------------
module _ where
 open import Data.Empty
 open import Data.Product
 open Properties public 

 in-dom-has-value : ∀ {s id} -> (h-dom : dom s id ≡ true) -> (∃ λ v -> s id ≡ just v)
 in-dom-has-value {s} {id} h-dom with (s id) 
 ... | just x = x , _≡_.refl

 -- Subterm relation on arithmetic terms implies vars inclusion.
 -- @TODO
 postulate
  ⊏ᵃ=>⊆ : ∀ (a₁ a : AExp) -> (sub : a₁ ⊏ᵃ a) -> (avars a₁ ⊆ avars a)
  ⊏ᵇᵇ=>⊆ : ∀ (b₁ b : BExp) -> (sub : b₁ ⊏ᵇ b) -> (bvars b₁ ⊆ bvars b)
  ⊏ᵇᵃ=>⊆ : ∀ (a : AExp) (b : BExp) -> (sub : a ⊏ᵇ b) -> (avars a ⊆ bvars b)
  ⊏ᶜᵃ=>⊆ : ∀ (a : AExp) (c : Command) -> (sub : a ⊏ᶜ c) -> (avars a ⊆ cvars c)
  ⊏ᶜᵇ=>⊆ : ∀ (b : BExp) (c : Command) -> (sub : b ⊏ᶜ c) -> (bvars b ⊆ cvars c)
  ⊏ᶜᶜ=>⊆ : ∀ (c₁ c : Command) -> (sub : c₁ ⊏ᶜ c) -> (cvars c₁ ⊆ cvars c)
