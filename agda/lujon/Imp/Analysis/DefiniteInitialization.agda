------------------------------------------------------------------------
-- Definite initialization analysis for IMP and its properties
------------------------------------------------------------------------
module Imp.Analysis.DefiniteInitialization where 

open import Size
open import Data.Or
open import Data.Bool
open import Imp.Syntax 
open import Data.Maybe 
open import Data.Product
open import Codata.Sized.Thunk 
open import Codata.Sized.Partial
open import Data.String hiding (_≈_)
open import Function using (case_of_)
open import Imp.Semantics.BigStep.Functional
open import Codata.Sized.Delay hiding (bind ; _⇓)
open import Codata.Sized.Partial.Relation.Binary.Convergence 
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


 open import Data.Empty
 open import Codata.Sized.Thunk
 open import Codata.Sized.Partial.Effectful 
 open import Codata.Sized.Partial.Bisimilarity
 open import Relation.Binary.PropositionalEquality
 open import Imp.Semantics.BigStep.Functional.Properties
 open import Codata.Sized.Partial.Bisimilarity.Relation.Binary.Equivalence using (≡=>≈)

 postulate 

  -- vars a ⊆ dom s -> ∃ v,  aval a s = Some v 
  adia-sound : ∀ (a : AExp) (s : Store) -> (dia : avars a ⊆ dom s) -> (∃ λ v -> aeval a s ≡ just v)

  -- vars b ⊆ dom s -> ∃ v, bval b s = Some v
  bdia-sound : ∀ (b : BExp) (s : Store) -> (dia : bvars b ⊆ dom s) -> (∃ λ v -> beval b s ≡ just v)

  dia-ceval=>⊆ : ∀ {v₁ v₂ : VarsSet} {s₁ s₂ : Store} {c : Command} (h-dia : Dia v₁ c v₂) 
   -> (h-⊆ : v₁ ⊆ dom s₁) -> (h-ceval⇓ : (ceval c s₁) ⇓ s₂) -> v₂ ⊆ dom s₂
 
 mutual 
  private 

   dia-sound-while-force : ∀ {x : Thunk (Delay (Maybe Store)) ∞} {c b s' v} (fx⇓s' : force x ⇓ s') 
    (dia : Dia v (while b c) v) (v⊆s : v ⊆ dom s')
    (s↯ : (bind (force x) (λ s -> later (ceval-while c b s))) ↯) -> ⊥
   dia-sound-while-force {x} {c} {b} {s'} {v} fx⇓s' dia v⊆s s↯ 
    with (force x) in eq-force-x
   ... | later x₁ with fx⇓s'
   ... | laterₗ lx⇓s' with s↯
   ... | laterₗ s↯' rewrite eq-force-x = dia-sound-while-later fx⇓s' dia v⊆s s↯ 
   dia-sound-while-force {x} {c} {b} {s'} {v} fx⇓s' dia v⊆s s↯ | now (just x₁) with fx⇓s' 
   ... | nowj x₁≡s' with s↯ 
   ... | laterₗ s↯' rewrite x₁≡s' = dia-sound (while b c) s' v v dia v⊆s s↯'

   dia-sound-while-later : ∀ {x c b s' v} (l⇓s' : later x ⇓ s') (dia : Dia v (while b c) v) (v⊆s : v ⊆ dom s')
    (s↯ : (bind (later x) (λ s -> later (ceval-while c b s))) ↯) -> ⊥
   dia-sound-while-later {x} {c} {b} {s'} {v} l⇓s' dia v⊆s s↯ 
    with l⇓s'
   ... | laterₗ fx⇓s' with (force x) in eq-force-x
   ... | later x₁  with fx⇓s'
   ... | laterₗ fx₁⇓s' with s↯
   ... | laterₗ s↯' rewrite eq-force-x with s↯' 
   ... | laterₗ s↯'' = dia-sound-while-force {x₁} fx₁⇓s' dia v⊆s s↯'' 
   dia-sound-while-later {x} {c} {b} {s'} {v} l⇓s' dia v⊆s s↯ | laterₗ fx⇓s' | now (just x₁) with fx⇓s'
   ... | nowj x₁≡s' rewrite x₁≡s' with s↯
   ... | laterₗ s↯' rewrite eq-force-x rewrite x₁≡s' with s↯'
   ... | laterₗ s↯'' = dia-sound (while b c) s' v v dia v⊆s s↯''


  dia-sound : ∀ (c : Command) (s : Store) (v v' : VarsSet) (dia : Dia v c v') (v⊆s : v ⊆ dom s)
   -> (h-err : (ceval c s) ↯) -> ⊥
  dia-sound (assign id a) s v .(id ↦ v) (assign .a .v .id a⊆v) v⊆s h-err 
   with (adia-sound a s (⊆-trans a⊆v v⊆s))
  ... | a' , eq-aeval rewrite eq-aeval rewrite eq-aeval with (h-err) 
  ... | ()
  dia-sound (ifelse b cᵗ cᶠ) s v .(vᵗ ∩ vᶠ) (if .b .v vᵗ vᶠ .cᵗ .cᶠ b⊆v diaᶠ diaᵗ) v⊆s h-err 
    with (bdia-sound b s λ x x-in-s₁ → v⊆s x (b⊆v x x-in-s₁))
  ... | false , eq-beval rewrite eq-beval rewrite eq-beval = dia-sound cᶠ s v vᶠ diaᶠ v⊆s h-err
  dia-sound (ifelse b cᵗ cᶠ) s v .(vᵗ ∩ vᶠ) (if .b .v vᵗ vᶠ .cᵗ .cᶠ b⊆v diaᶠ diaᵗ) v⊆s h-err 
   | true , eq-beval rewrite eq-beval rewrite eq-beval = dia-sound cᵗ s v vᵗ diaᵗ v⊆s h-err
  dia-sound (seq c₁ c₂) s v₁ v₃ dia v⊆s h-err 
   with dia 
  ... | seq .v₁ v₂ .v₃ .c₁ .c₂ dia-c₁ dia-c₂
   with (ceval-result c₁ s)
  ... | left c⇑ = ⇑->↯=>⊥ {c = (seq c₁ c₂)} {s = s} (⊏ᶜ=>⇑ {s = s} {s' = s} (λ x x-in-s₁ → x-in-s₁) (seq-l c₁ c₂) c⇑ ) h-err
  ... | right (right c₁↯) = dia-sound c₁ s v₁ v₂ dia-c₁ v⊆s c₁↯ 
  ... | right (left (s' , c₁⇓s')) = 
   dia-sound c₂ s' v₂ v₃ dia-c₂ (dia-ceval=>⊆ dia-c₁ v⊆s c₁⇓s') (bind-↯ c₁⇓s' h-err)
  dia-sound (while b c) s v v' dia v⊆s h-err  
   with dia
  ... | while .b .v v₁ .c b⊆s dia-c
   with (bdia-sound b s (λ x x-in-s₁ → v⊆s x (b⊆s x x-in-s₁)))
  ... | false , eq-beval rewrite eq-beval rewrite eq-beval = case h-err of λ ()
  ... | true , eq-beval 
   with (ceval-result c s) 
  ... | left c⇑ = ⇑->↯=>⊥ {c = (while b c)} {s = s} (⊏ᶜ=>⇑ {s = s} {s' = s} (λ x x-in-s₁ → x-in-s₁) (while-c b c) c⇑ ) h-err
  ... | right (right c↯) = dia-sound c s v v₁ dia-c v⊆s c↯ 
  ... | right (left (s' , c⇓s')) with (ceval c s) in eq-ceval-c
  ... | now (just x) with (c⇓s') 
  ... | nowj x≡s' rewrite eq-beval rewrite eq-ceval-c with h-err
  ... | laterₗ n rewrite x≡s' = dia-sound (while b c) s' v v dia (⊆-trans v⊆s (ceval=>⊆ c s s' eq-ceval-c)) n
  dia-sound (while b c) s v v' dia v⊆s h-err 
   | while .b .v v₁ .c b⊆s dia-c
   | true , eq-beval 
   | right (left (s' , c⇓s')) 
   | later x rewrite eq-beval rewrite eq-beval with h-err
  ... | laterₗ s↯'  with c⇓s'
  ... | laterₗ fx⇓s' = dia-sound-while-force {x} fx⇓s' dia (⊆-trans v⊆s (ceval-⇓=>⊆ c s s' (≡=>⇓ eq-ceval-c c⇓s'))) s↯'
