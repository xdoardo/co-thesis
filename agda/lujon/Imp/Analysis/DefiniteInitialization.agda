------------------------------------------------------------------------
-- Definite initialization analysis for IMP and its properties
------------------------------------------------------------------------
module Imp.Analysis.DefiniteInitialization where 

open import Data.Bool
open import Imp.Syntax 
open import Data.Maybe 
open import Codata.Sized.Thunk 
open import Data.String hiding (_≈_)
open import Function using (case_of_)
open import Imp.Semantics.BigStep.Functional
---


data Dia : VarsSet -> Command -> VarsSet -> Set where 
 skip : ∀ (v : VarsSet) -> Dia v (skip) v
 assign : ∀ a v id (a⊆v : (avars a) ⊆ v) -> Dia v (assign id a) (id ↦ v)
 seq : ∀ v₁ v₂ v₃ c₁ c₂ -> (relc₁ : Dia v₁ c₁ v₂) -> 
  (relc₂ : Dia v₂ c₂ v₃) -> Dia v₁ (seq c₁ c₂) v₃ 
 if : ∀ b v vᵗ vᶠ cᵗ cᶠ (b⊆v : (bvars b) ⊆ v) -> (relcᶠ : Dia v cᶠ vᶠ) -> 
  (relcᵗ : Dia v cᵗ vᵗ) -> Dia v (ifelse b cᵗ cᶠ) (vᵗ ∩ vᶠ)
 while : ∀ b v v₁ c -> (b⊆s : (bvars b) ⊆ v) -> (relc : Dia v c v₁) -> Dia v (while b c) v


--------------------------------------------------
-- Properties of definite initialization analysis 
--------------------------------------------------
module _ where

  open import Size
  open import Data.Or
  open import Data.And
  open import Data.Empty
  open import Data.Product
  open import Codata.Sized.Thunk
  open import Codata.Sized.Partial
  open import Codata.Sized.Partial.Effectful 
  open import Codata.Sized.Partial.Bisimilarity
  open import Relation.Binary.PropositionalEquality 
  open import Codata.Sized.Delay hiding (bind ; _⇓)
  open Relation.Binary.PropositionalEquality.≡-Reasoning
  open import Imp.Semantics.BigStep.Functional.Properties
  open import Codata.Sized.Partial.Relation.Unary.Convergence
  open import Codata.Sized.Partial.Relation.Binary.Convergence 



  -- @TODO
  postulate 

   -- vars a ⊆ dom s -> ∃ v,  aval a s = Some v 
   adia-safe : ∀ (a : AExp) (s : Store) -> (dia : avars a ⊆ dom s) -> (∃ λ v -> aeval a s ≡ just v)

   -- vars b ⊆ dom s -> ∃ v, bval b s = Some v
   bdia-safe : ∀ (b : BExp) (s : Store) -> (dia : bvars b ⊆ dom s) -> (∃ λ v -> beval b s ≡ just v)

   dia-ceval=>⊆ : ∀ {i} (v₁ v₂ : VarsSet) (s₁ s₂ : Store) (c : Command) -> (h-dia : Dia v₁ c v₂) 
    -> (h-⊆ : v₁ ⊆ dom s₁) -> (h-ceval⇓ : i ⊢ ceval c s₁ ⇓ s₂) -> v₂ ⊆ dom s₂




  private

   seq⇓-bind : ∀ {i} (c₁ c₂ : Command) (s s' sᶠ : Store) -> (h-c₁ : i ⊢ ceval {i} c₁ s ⇓ s') 
    -> (h-c₂ : i ⊢ ceval {i} c₂ s' ⇓ sᶠ) -> i ⊢ bind (ceval {i} c₁ s) (ceval {i} c₂) ⇓ sᶠ
   seq⇓-bind {i} c₁ c₂ s s' sᶠ h-c₁ h-c₂ with (ceval {i} c₁ s) in eq-ceval
   ... | Delay.later x  with (h-c₁) in eq-h-c₁
   ... | later⇓ v rewrite eq-ceval = later⇓ ? 
   seq⇓-bind c₁ c₂ s s' sᶠ h-c₁ h-c₂ | Delay.now (just x₁) with (h-c₁) 
   ... | now⇓ = h-c₂
 


  mutual
   private 
    dia-while : ∀ {i} (c : Command) (b : BExp) (s : Store) (v : VarsSet) (dia : Dia v (while b c) v) (v⊆s : v ⊆ dom s) 
     (eq-beval : (beval b s) ≡ just true) -> XOr (i ⊢ (ceval (while b c) s) ⇑) (i ⊢ (ceval (while b c) s) ⇓) 
    dia-while {i} c b s v dia v⊆s eq-beval with (dia) 
    ... | while .b .v v₁ .c b⊆s dia-c₁ with (dia-sound {i} c s v v₁ dia-c₁ v⊆s) 
    ... | left c⇑  = left (⊏ᶜ=>⇑ {s} {s} (λ x x-in-s₁ → x-in-s₁) c (while b c) (while-c b c) c⇑)
    ... | right (s' , c⇓s') with (ceval {i} c s) in eq-ceval-c
    ... | later x = {! !}
    ... | now (just x) with (c⇓s') 
    ... | now⇓ rewrite eq-beval rewrite eq-ceval-c = ∞dia-while-now {i} c b s x v dia v⊆s eq-beval eq-ceval-c  

    ∞dia-while-now : ∀ {i} (c : Command) (b : BExp) (s s' : Store) (v : VarsSet) (dia : Dia v (while b c) v) (v⊆s : v ⊆ dom s) 
     (eq-beval : (beval b s) ≡ just true) (h-ceval-c : (ceval {i} c s) ≡ now (just s'))
     -> XOr (i ⊢ (later (ceval-while c b s')) ⇑) (i ⊢ (later (ceval-while c b s')) ⇓) 
    ∞dia-while-now c b s s' v dia v⊆s eq-beval h-ceval-c = {! !}


   dia-sound : ∀ {i} (c : Command) (s : Store) (v v' : VarsSet) -> (dia : Dia v c v') 
    -> (v⊆s : v ⊆ dom s) -> XOr (i ⊢ (ceval c s) ⇑) (i ⊢ (ceval c s) ⇓)
   dia-sound {i} skip s v v' dia v⊆s = right (s , now⇓)
   dia-sound {i} (assign id a) s v .(id ↦ v) (assign .a .v .id a⊆v) v⊆s 
    with (adia-safe a s (⊆-trans a⊆v v⊆s))
   ... | v₁ , eq-aeval rewrite eq-aeval = right ((update id v₁ s) , now⇓) 
   dia-sound {i} (ifelse b cᵗ cᶠ) s v .(vᵗ ∩ vᶠ) (if .b .v vᵗ vᶠ .cᵗ .cᶠ b⊆v diaᶠ diaᵗ) v⊆s
    with (bdia-safe b s λ x x-in-s₁ → v⊆s x (b⊆v x x-in-s₁))
   ... | false , eq-beval rewrite eq-beval with (dia-sound {i} cᶠ s v vᶠ diaᶠ v⊆s) 
   ... | n = n
   dia-sound {i} (ifelse b cᵗ cᶠ) s v .(vᵗ ∩ vᶠ) (if .b .v vᵗ vᶠ .cᵗ .cᶠ b⊆v diaᶠ diaᵗ) v⊆s
    | true , eq-beval rewrite eq-beval with (dia-sound {i} cᵗ s v vᵗ diaᵗ v⊆s) 
   ... | n = n
   dia-sound {i} (seq c₁ c₂) s v₁ v₃ (seq .v₁ v₂ .v₃ .c₁ .c₂ dia-c₁ dia-c₂) v⊆s 
    with (dia-sound {i} c₁ s v₁ v₂ dia-c₁ v⊆s)
   ... | left c₁⇑ = left (⊏ᶜ=>⇑ {s} {s} (λ x x-in-s₁ → x-in-s₁) c₁ (seq c₁ c₂) (seq-l c₁ c₂) c₁⇑)
   ... | right (s' , ceval-c₁⇓s') 
    with (dia-sound {i} c₂ s' v₂ v₃ dia-c₂ (dia-ceval=>⊆ v₁ v₂ s s' c₁ dia-c₁ v⊆s ceval-c₁⇓s'))
   ... | left h-c₂⇑  = left (⊏ᶜ=>⇑ {s} {s'} (ceval=>⊆ c₁ s s' ceval-c₁⇓s') c₂ (seq c₁ c₂) (seq-r c₁ c₂) h-c₂⇑)
   ... | right (sᶠ , ceval-c₂⇓sᶠ) = right (sᶠ , (seq⇓-bind {i} c₁ c₂ s s' sᶠ ceval-c₁⇓s' ceval-c₂⇓sᶠ))
   dia-sound {i} (while b c) s v v' dia v⊆s with (dia) 
   ... | while .b .v v₁ .c b⊆s n with (bdia-safe b s λ x x-in-s₁ → v⊆s x (b⊆s x x-in-s₁)) 
   ... | false , eq-beval rewrite eq-beval = right (s , now⇓) 
   ... | true , eq-beval = dia-while {i} c b s v dia v⊆s eq-beval 
