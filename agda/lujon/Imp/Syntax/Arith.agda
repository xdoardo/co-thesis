------------------------------------------------------------------------
-- Arithmetic expressions of Imp
------------------------------------------------------------------------
module Imp.Syntax.Arith where 

open import Data.List
open import Data.Integer using (ℤ ; 0ℤ)
open import Imp.Syntax.Ident using (Ident ; Store ; empty ; update ; join ; _⊆ᵤ_)
open import Data.String using (_==_)
open import Data.Bool using (if_then_else_)
open import Data.Maybe
--- 

data AExp : Set where 
 const : (n : ℤ) -> AExp
 var   : (id : Ident) -> AExp 
 plus  : (a₁ : AExp) -> (a₂ : AExp) -> AExp

vars-aexp : (a : AExp) -> Store
vars-aexp (const n) = empty
vars-aexp (var id) = update id 0ℤ empty
vars-aexp (plus a a₁) = join (vars-aexp a) (vars-aexp a₁)

------------------------------------------------------------------------
-- Properties of arithmetic expressions 
------------------------------------------------------------------------
module _ where
 open import Data.Maybe 
 open import Data.Product
 open import Relation.Binary.PropositionalEquality
 --- 
 
 -- Subexpression relation
 data _⊆ᵃ_ : {A : Set} -> A -> AExp -> Set where
  refl : ∀ (a : AExp) -> a ⊆ᵃ a
  plus-l : ∀ (a a₁ : AExp) -> a ⊆ᵃ (plus a a₁)
  plus-r : ∀ (a a₁ : AExp) -> a₁ ⊆ᵃ (plus a a₁)
 
 
 ⊆ᵃ-⊆ᵤ : ∀ a a₁ -> (a⊆a₁ : a ⊆ᵃ a₁) -> (vars-aexp a) ⊆ᵤ (vars-aexp a₁)
 ⊆ᵃ-⊆ᵤ a .a (refl .a) id x = x
 ⊆ᵃ-⊆ᵤ a .(plus a a₁) (plus-l .a a₁) id x with (vars-aexp (plus a a₁)) | (vars-aexp a)
 ... | s | s' with (s id) | (s' id)
 ... | just x₁ | just x₂ = x₂ , refl
 ... | nothing | just x₁ = x₁ , refl
 ⊆ᵃ-⊆ᵤ a .(plus a₁ a) (plus-r a₁ .a) id x with (vars-aexp (plus a a₁)) | (vars-aexp a₁) | (vars-aexp a)
 ... | s | s₁' | s' with (s id) | (s₁' id) | (s' id) in eq-s'-id
 ... | just x₁ | just x₂ | just x₃ = x₂ , refl
 ... | just x₁ | nothing | just x₂ = x₂ , eq-s'-id
 ... | nothing | just x₁ | just x₂ = x₁ , refl
 ... | nothing | nothing | just x₁ = x₁ , eq-s'-id

