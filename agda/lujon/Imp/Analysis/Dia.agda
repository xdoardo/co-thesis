------------------------------------------------------------------------
-- Definite initialization analysis for IMP and its properties
------------------------------------------------------------------------
module Imp.Analysis.Dia where 

open import Size
open import Data.Or
open import Data.Bool
open import Imp.Syntax 
open import Data.Maybe 
open import Codata.Sized.Thunk 
open import Codata.Sized.Partial
open import Data.String hiding (_≈_)
open import Function using (case_of_)
open import Imp.Semantics.BigStep.Functional
open import Codata.Sized.Delay hiding (bind ; _⇓)
open import Codata.Sized.Partial.Relation.Unary.Convergence
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


data Result : (c : Command) (s : Store) (i : Size) -> Set where 
 now-r : ∀ c s {i} -> XOr (i ⊢ (ceval {i} c s) ⇑) (i ⊢ (ceval {i} c s) ⇓) -> Result c s i 
 later-r : ∀ c s {i} (d : Thunk (Result c s) i) -> Result c s i

--------------------------------------------------
-- Properties of definite initialization analysis 
--------------------------------------------------
module _ where


 open import Data.Product
 open import Codata.Sized.Thunk
 open import Codata.Sized.Partial.Effectful 
 open import Codata.Sized.Partial.Bisimilarity
 open import Relation.Binary.PropositionalEquality
 open import Imp.Semantics.BigStep.Functional.Properties

 postulate 

  -- vars a ⊆ dom s -> ∃ v,  aval a s = Some v 
  adia-sound : ∀ (a : AExp) (s : Store) -> (dia : avars a ⊆ dom s) -> (∃ λ v -> aeval a s ≡ just v)

  -- vars b ⊆ dom s -> ∃ v, bval b s = Some v
  bdia-sound : ∀ (b : BExp) (s : Store) -> (dia : bvars b ⊆ dom s) -> (∃ λ v -> beval b s ≡ just v)

  dia-ceval=>⊆ : ∀ {i} (v₁ v₂ : VarsSet) (s₁ s₂ : Store) (c : Command) -> (h-dia : Dia v₁ c v₂) 
   -> (h-⊆ : v₁ ⊆ dom s₁) -> (h-ceval⇓ : i ⊢ (ceval c s₁) ⇓ s₂) -> v₂ ⊆ dom s₂


 private 
  while-false : ∀ {i} (c : Command) (b : BExp) (s : Store) (h-b : beval b s ≡ just false) 
   -> i ⊢ (ceval {i} (while b c) s) ⇓ s
  while-false c b s h-b rewrite h-b = now⇓
 
  assign-v : ∀ {i} (id : Ident) (a : AExp) (s : Store) v (h-a : aeval a s ≡ just v)
   -> i ⊢ (ceval {i} (assign id a) s) ⇓ (update id v s)
  assign-v id a s v h-a rewrite h-a = now⇓
 
  ceval≡now=>⇓ : ∀ {i} (c : Command) (s s' : Store) (h : ceval {i} c s ≡ now (just s'))
   -> i ⊢ ceval {i} c s ⇓ s'
  ceval≡now=>⇓ c s s' h rewrite h = now⇓
  
  ceval≡=>⇓ : ∀ {i} c s s' x (h : ceval c s ≡ x) (h1 : i ⊢ x ⇓ s') -> i ⊢ (ceval c s) ⇓ s'
  ceval≡=>⇓ c s s' x h h1 rewrite h = h1

 mutual 
  dia-sound : ∀ {i} (c : Command) (s : Store) (v v' : VarsSet) (dia : Dia v c v') (v⊆s : v ⊆ dom s)
   -> Result c s i
  dia-sound skip s v v' dia v⊆s = now-r skip s (right (s , now⇓))
  dia-sound (assign id a) s v .(id ↦ v) (assign .a .v .id a⊆v) v⊆s 
   with (adia-sound a s λ x x-in-s₁ → v⊆s x (a⊆v x x-in-s₁))
  ... | e , eq-aeval rewrite eq-aeval = now-r (assign id a) s (right ((update id e s) , assign-v id a s e eq-aeval))
  dia-sound (ifelse b c c₁) s v v' dia v⊆s = {! !}
  dia-sound (seq c c₁) s v v' dia v⊆s = {! !}
  dia-sound {i} (while b c) s v v' dia v⊆s 
   with dia 
  ... | while .b .v v₁ .c b⊆s dia-c 
   with (bdia-sound b s λ x x-in-s₁ → v⊆s x (b⊆s x x-in-s₁))
  ... | false , eq-beval = now-r (while b c) s (right (s , (while-false c b s eq-beval)))
  ... | true , eq-beval = dia-while {i} c v b s dia v⊆s eq-beval

  private 
   dia-while : ∀ {i} (c : Command) (v : VarsSet) (b : BExp) (s : Store) 
    (dia : Dia v (while b c) v) (v⊆s : v ⊆ dom s) (h-b : beval b s ≡ just true) 
    -> Result (while b c) s i
   dia-while {i} c v b s dia v⊆s h-b with dia
   ... | while .b .v v₁ .c b⊆s dia-c with (dia-sound {i} c s v v₁ dia-c v⊆s) 
   ... | now-r .c .s (left c⇑) = now-r (while b c) s (left (⊏ᶜ=>⇑ (λ x x-in-s₁ → x-in-s₁) c (while b c) (while-c b c) c⇑))
   ... | later-r .c .s d = ? 
   ... | now-r .c .s (right (s' , c⇓s')) with (ceval {i} c s)  in eq-ceval
   ... | now (just x) = ?
   ... | later x = ?

   while-now-r-now : ∀ {i} (c : Command) (v : VarsSet) (b : BExp) (s s' : Store) 
    (dia : Dia v (while b c) v) (v⊆s : v ⊆ dom s) (h-b : beval b s ≡ just true) 
    -> (h-c : i ⊢ ceval {i} c s ⇓ s') -> (h-now : ceval {i} c s ≡ now (just s'))
    -> Result (while b c) s i
   while-now-r-now {i} c v b s s' dia v⊆s h-b h-c h-now rewrite h-b rewrite h-now = later-r (while b c) s ?

   ceval-while-result : ∀ {i} (c : Command) (v : VarsSet) (b : BExp) (s s' : Store) 
    (dia : Dia v (while b c) v) (v⊆s : v ⊆ dom s) (h-b : beval b s ≡ just true) 
    -> (h-c : i ⊢ ceval {i} c s ⇓ s') -> (h-now : ceval {i} c s ≡ now (just s'))
    -> Thunk (Result (while b c) s') i
   force (ceval-while-result {i} c v b s s' dia v⊆s h-b h-c h-now) {j} =  
    dia-sound (while b c) s' v v dia (⊆-trans v⊆s (ceval=>⊆ {i} c s s' h-c))



