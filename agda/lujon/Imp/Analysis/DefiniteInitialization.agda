------------------------------------------------------------------------
-- Definite initialization analysis for IMP and its properties
------------------------------------------------------------------------
module Imp.Analysis.DefiniteInitialization where 

open import Data.Bool
open import Imp.Syntax 
open import Data.Maybe 
open import Codata.Sized.Thunk 
open import Data.String hiding (_≈_)
open import Imp.Semantics.BigStep.Functional
---


data Dia : VarsSet -> Command -> VarsSet -> Set where 
 skip : ∀ (v : VarsSet) -> Dia v (skip) v
 assign : ∀ a v id (a⊆v : (avars a) ⊆ v) -> Dia v (assign id a) (id ↦ v)
 seq : ∀ v₁ v₂ v₃ c₁ c₂ -> (relc₁ : Dia v₁ c₁ v₂) -> 
  (relc₂ : Dia v₂ c₂ v₃) -> Dia v₁ (seq c₁ c₂) v₃ 
 if : ∀ b v vᵗ vᶠ cᵗ cᶠ (b⊆v : (bvars b) ⊆ v) -> (relcᶠ : Dia v cᶠ vᶠ) -> 
  (relcᵗ : Dia v cᵗ vᵗ) -> Dia v (ifelse b cᵗ cᶠ) (vᵗ ∩ vᶠ)
 while : ∀ b v v₁ c -> (b⊆s : (bvars b) ⊆ v) -> (relc : Dia v c v₁) -> Dia v (while b c) v₁


--------------------------------------------------
-- Properties of definite initialization analysis 
--------------------------------------------------
module _ where

  open import Data.Or
  open import Data.And
  open import Data.Product
  open import Codata.Sized.Delay using (Delay)
  open import Relation.Binary.PropositionalEquality 
  open import Codata.Sized.Partial.Relation.Unary.Convergence
  open import Codata.Sized.Partial.Relation.Binary.Convergence 
  open Relation.Binary.PropositionalEquality.≡-Reasoning
  open import Codata.Sized.Partial.Effectful 
  open import Codata.Sized.Partial.Bisimilarity
  open import Imp.Semantics.BigStep.Functional.Properties



  postulate 
   -- vars a ⊆ dom s -> ∃ v,  aval a s = Some v 
   adia-safe : ∀ (a : AExp) (s : Store) -> (dia : avars a ⊆ dom s) -> (∃ λ v -> aeval a s ≡ just v)

   -- vars b ⊆ dom s -> ∃ v, bval b s = Some v
   bdia-safe : ∀ (b : BExp) (s : Store) -> (dia : bvars b ⊆ dom s) -> (∃ λ v -> beval b s ≡ just v)

   dia=>⊆ : ∀ (v₁ v₂ : VarsSet) {c : Command} -> (h-dia : Dia v₁ c v₂) -> v₁ ⊆ v₂

   dia-ceval=>⊆ : ∀ (v₁ v₂ : VarsSet) (s₁ s₂ : Store) (c : Command) -> (h-dia : Dia v₁ c v₂) 
    -> (h-⊆ : v₁ ⊆ dom s₁) -> (h-ceval⇓ : ceval c s₁ ⇓ s₂) -> v₂ ⊆ dom s₂


  dia-sound : ∀ (c : Command) (s : Store) (v v' : VarsSet) -> (dia : Dia v c v') -> (v⊆s : v ⊆ dom s) 
    -> XOr ((ceval c s)⇑) ((ceval c s)⇓)
  dia-sound skip s v v' dia v⊆s = right (s , now⇓)
  dia-sound (assign id a) s v .(id ↦ v) (assign .a .v .id a⊆v) v⊆s 
   with (adia-safe a s (⊆-trans a⊆v v⊆s)) 
  ... | v₁ , aeval-eq rewrite aeval-eq = right ((update id v₁ s) , now⇓)
  dia-sound (seq c₁ c₂) s v₁ v₃ (seq .v₁ v₂ .v₃ .c₁ .c₂ dia-c₁ dia-c₂) v⊆s 
   with (dia-sound c₁ s v₁ v₂ dia-c₁ v⊆s)
  ... | left h-c₁⇑  = left (⊏ᶜ=>⇑ {s} {s} (λ x x-in-s₁ → x-in-s₁) c₁ (seq c₁ c₂) (seq-l c₁ c₂) h-c₁⇑)
  ... | right ex-c₁⇓  with ex-c₁⇓
  ... | s' , ceval-c₁⇓s' with (dia-sound c₂ s' v₂ v₃ dia-c₂ (dia-ceval=>⊆ v₁ v₂ s s' c₁ dia-c₁ v⊆s ceval-c₁⇓s'))
  ... | left h-c₂⇑  = left (⊏ᶜ=>⇑ {s} {s'} (ceval=>⊆ c₁ s s' ceval-c₁⇓s') c₂ (seq c₁ c₂) (seq-r c₁ c₂) h-c₂⇑)
  ... | right ex-c₂⇓ with ex-c₂⇓
  ... | sᶠ , ceval-c₂⇓sᶠ = right (sᶠ , ?)
  dia-sound (ifelse b c c₁) s v .(vᵗ ∩ vᶠ) (if .b .v vᵗ vᶠ .c .c₁ b⊆v dia dia₁) v⊆s 
   with (bdia-safe b s (λ x x-in-s₁ → v⊆s x (b⊆v x x-in-s₁)))
  ... | false , eq-beval 
   rewrite eq-beval with (dia-sound c₁ s v vᶠ dia v⊆s) 
  ... | n = n
  dia-sound (ifelse b c c₁) s v .(vᵗ ∩ vᶠ) (if .b .v vᵗ vᶠ .c .c₁ b⊆v dia dia₁) v⊆s | true , eq-beval
   rewrite eq-beval with (dia-sound c s v vᵗ dia₁ v⊆s)
  ... | n = n
  dia-sound (while b c) s v v' (while .b .v .v' .c b⊆s dia) v⊆s 
   with (bdia-safe b s (λ x x-in-s₁ → v⊆s x (b⊆s x x-in-s₁)))
  ... | false , eq-beval rewrite eq-beval = right (s , now⇓)
  ... | true , eq-beval rewrite eq-beval with (dia-sound c s v v' dia v⊆s) 
  ... | left ceval-c⇑ = left ? 
  ... | right ceval-c⇓ with ceval-c⇓ 
  ... | s' , snd = ?  
