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
cvars (assign id a) = avars a
cvars (seq c c₁) = (cvars c) ∪ (cvars c₁)
cvars (ifelse b c c₁) = ((bvars b) ∪ (cvars c)) ∪ (cvars c₁)
cvars (while b c) = (bvars b) ∪ (cvars c)

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

 private
  postulate
   -- We must postulate extensionality.
   ext : ∀ a b -> Extensionality a b
   true-or-false : (true ∨ false) ≡ false -> ⊥
 
 -- Extensional equality for VarsSet.
 vars-ext : ∀ {s₁ s₂ : VarsSet} -> (a-ex : ∀ x -> s₁ x ≡ s₂ x) -> s₁ ≡ s₂
 vars-ext a-ex = ext Agda.Primitive.lzero Agda.Primitive.lzero a-ex
 
 vars-id-has-id : ∀ id -> (h : (avars (var id)) id ≡ false) -> ⊥
 vars-id-has-id id h with (==-refl {id})
 ... | r rewrite r = true-or-false h

 in-dom-has-value : ∀ {s id} -> (h-dom : dom s id ≡ true) -> (∃ λ v -> s id ≡ just v)
 in-dom-has-value {s} {id} h-dom with (s id) 
 ... | just x = x , _≡_.refl

 -- Subterm relation on arithmetic terms implies vars inclusion.
 -- @TODO
 postulate
  ⊑ᵃ=>⊆ : ∀ (a₁ a : AExp) -> (sub : a₁ ⊑ᵃ a) -> (avars a₁ ⊆ avars a)
  ⊑ᵇᵇ=>⊆ : ∀ (b₁ b : BExp) -> (sub : b₁ ⊑ᵇ b) -> (bvars b₁ ⊆ bvars b)
  ⊑ᵇᵃ=>⊆ : ∀ (a : AExp) (b : BExp) -> (sub : a ⊑ᵇ b) -> (avars a ⊆ bvars b)
  ⊑ᶜᵃ=>⊆ : ∀ (a : AExp) (c : Command) -> (sub : a ⊑ᶜ c) -> (avars a ⊆ cvars c)
  ⊑ᶜᵇ=>⊆ : ∀ (b : BExp) (c : Command) -> (sub : b ⊑ᶜ c) -> (bvars b ⊆ cvars c)
  ⊑ᶜᶜ=>⊆ : ∀ (c₁ c : Command) -> (sub : c₁ ⊑ᶜ c) -> (cvars c₁ ⊆ cvars c)
