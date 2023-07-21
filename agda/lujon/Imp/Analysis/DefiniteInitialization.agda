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
 assign : ∀ a v id (a⊆s : (avars a) ⊆ v) -> Dia v (assign id a) (id ↦ v)
 seq : ∀ v₁ v₂ v₃ c₁ c₂ -> (relc₁ : Dia v₁ c₁ v₂) -> 
  (relc₂ : Dia v₂ c₂ v₃) -> Dia v₁ (seq c₁ c₂) v₃ 
 if : ∀ b v vᵗ vᶠ cᵗ cᶠ (b⊆s : (bvars b) ⊆ v) -> (relcᶠ : Dia v cᶠ vᶠ) -> 
  (relcᵗ : Dia v cᵗ vᵗ) -> Dia v (ifelse b cᵗ cᶠ) (vᵗ ∩ vᶠ)
 while : ∀ b v v₁ c -> (b⊆s : (bvars b) ⊆ v) -> (relc : Dia v c v₁) -> Dia v (while b c) v₁

private
 cdia-inner : (c : Command) -> (s : VarsSet) -> VarsSet
 cdia-inner skip s = ∅ 
 cdia-inner (assign id a) s with (adia a s)  -- vars a ⊆ (dom s)
 ... | false =  ∅ 
 ... | true =  (id ↦ s)
 cdia-inner (seq c c₁) s =  cdia-inner c₁ (cdia-inner c s)
 cdia-inner (ifelse b c c₁) s with (bdia b s)
 ... | false = ∅ 
 ... | true = (cdia-inner c s) ∩ (cdia-inner c₁ s) 
 cdia-inner (while b c) s with (bdia b s) 
 ... | false =  ∅ 
 ... | true = s 


-- Computes the set of definitely initialized variables
ivars : Command -> VarsSet
ivars c = cdia-inner c ∅ 

-- Checks that only initialized variable are accessed
ok : (c : Command) -> (s : VarsSet) -> Bool 
ok skip s = true
ok (assign id a) s = adia a s 
ok (seq c c₁) s = (ok c s) ∧ (ok c s)
ok (ifelse b c c₁) s = (bdia b s) ∧ (ok c s) ∧ (ok c₁ s)
ok (while b c) s = (bdia b s) ∧ (ok c s)

--------------------------------------------------
-- Properties of definite initialization analysis 
--------------------------------------------------
module _ where

  open import Data.Or
  open import Data.And
  open import Data.Product
  open import Relation.Binary.PropositionalEquality 
  open import Codata.Sized.Partial.Relation.Unary.Convergence

  dia-ok : ∀ (c : Command) (A A' : VarsSet) -> (h : Dia A c A') -> And (A' ≡ (A ∪ cvars c)) (ok A c ≡ true)
  dia-ok = ?

  ok-dia : ∀ (c : Command) (A : VarsSet) -> (h : ok A c ≡ true) -> Dia A c (A ∪ cvars c)
  ok-dia = ?

  -- vars a ⊆ dom s -> ∃ v,  aval a s = Some v 
  adia-safe : ∀ (a : AExp) (s : Store) -> (dia : avars a ⊆ dom s) -> (∃ λ v -> aeval a s ≡ just v)
  adia-safe = ?

  -- vars b ⊆ dom s -> ∃ v, bval b s = Some v
  bdia-safe : ∀ (b : BExp) (s : Store) -> (dia : bvars b ⊆ dom s) -> (∃ λ v -> beval b s ≡ just v)
  bdia-safe = ?

  -- D is increasing. 
  dia-inc : ∀ (A A' : VarsSet) {c} -> (rel : Dia A c A') -> A ⊆ A'
  dia-inc = ?

  dia-sound : ∀ (c : Command) (s s' : Store) (A A' : VarsSet) -> (dia : Dia A c A') -> (A⊆s : A ⊆ dom s) 
    -> Or ((ceval c s)⇑) ((ceval c s)⇓)
  dia-sound = ?
