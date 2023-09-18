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
open import Data.CharacteristicFunction (String) (_==_) renaming (CharacteristicFunction to VarsSet) public
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
cvars (ifelse b c c₁) = (cvars c) ∩ (cvars c₁)
cvars (while b c) =  ∅

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

 -- Subterm relation on arithmetic terms implies vars inclusion.
 -- @TODO
 postulate
  ⊏ᵃ=>⊆ : ∀ (a₁ a : AExp) -> (sub : a₁ ⊏ᵃ a) -> (avars a₁ ⊆ avars a)
  ⊏ᵇᵇ=>⊆ : ∀ (b₁ b : BExp) -> (sub : b₁ ⊏ᵇ b) -> (bvars b₁ ⊆ bvars b)
  ⊏ᵇᵃ=>⊆ : ∀ (a : AExp) (b : BExp) -> (sub : a ⊏ᵇ b) -> (avars a ⊆ bvars b)
  ⊏ᶜᵃ=>⊆ : ∀ (a : AExp) (c : Command) -> (sub : a ⊏ᶜ c) -> (avars a ⊆ cvars c)
  ⊏ᶜᵇ=>⊆ : ∀ (b : BExp) (c : Command) -> (sub : b ⊏ᶜ c) -> (bvars b ⊆ cvars c)
  ⊏ᶜᶜ=>⊆ : ∀ (c₁ c : Command) -> (sub : c₁ ⊏ᶜ c) -> (cvars c₁ ⊆ cvars c)

 cvars-skip : (cvars skip) ≡ ∅ 
 cvars-skip = refl

 cvars-assign : ∀ {id a} -> (cvars (assign id a)) ≡ id ↦ ∅
 cvars-assign = refl

 cvars-seq : ∀ {c₁ c₂} -> (cvars (seq c₁ c₂)) ≡ (cvars c₁) ∪ (cvars c₂)
 cvars-seq = refl

 cvars-if : ∀ {b c₁ c₂} -> (cvars (ifelse b c₁ c₂)) ≡ (cvars c₁) ∩ (cvars c₂)
 cvars-if = refl
 
 cvars-while : ∀ {b c} -> (cvars (while b c)) ≡ ∅ 
 cvars-while = refl

 -------------------------------------------------
 -- Properties relating the Store type and VarsSet
 -------------------------------------------------

 in-dom-has-value : ∀ {s id} -> (h-dom : dom s id ≡ true) -> (∃ λ v -> s id ≡ just v)
 in-dom-has-value {s} {id} h-dom with (s id) 
 ... | just x = x , _≡_.refl

 dom-store≡ : ∀ {s s' : Store} -> (h≡ : s ≡ s') -> dom s ≡ dom s'
 dom-store≡ h≡ rewrite h≡ = refl

 empty-is-∅ : dom empty ≡ ∅
 empty-is-∅ = refl
 
 private
  update-is-↦-ext : ∀ {x s id v} -> dom (update id v s) x ≡ (id ↦ dom s) x
  update-is-↦-ext {x} {s} {id} {v} with id == x in eq-id
  ... | true = refl
  ... | false with (s x) in eq-sid
  ... | just x₁ = refl
  ... | nothing = refl

 update-is-↦ : ∀ {s id v} -> dom (update id v s) ≡ id ↦ dom s
 update-is-↦ {s} {id} {v} = if-ext λ { x → update-is-↦-ext {x} {s} {id} {v} } 


 private
  ↦-is-∪-ext : ∀ {x id s} -> (id ↦ s) x ≡ (s ∪ (id ↦ ∅)) x
  ↦-is-∪-ext {x} {id} {s} with (id == x) in eq-id | (s x)
  ... | false | false = refl
  ... | false | true = refl
  ... | true | false = refl
  ... | true | true = refl

 ↦-is-∪ : ∀ {id s} -> (id ↦ s) ≡ (s ∪ (id ↦ ∅))
 ↦-is-∪ {id} {s} = if-ext λ { x → ↦-is-∪-ext {x} {id} {s} } 
