------------------------------------------------------------------------
-- Boolean expressions of IMP
------------------------------------------------------------------------
module Imp.Syntax.Bool where 

open import Imp.Syntax.Arith
open import Data.Bool hiding (not)
open import Data.List using (_∷_ ; _++_ ; List ; [] )
open import Imp.Syntax.Ident using (Ident ; Store ; empty ; update ; join ; _⊆ᵤ_)
---

data BExp : Set where 
 const : (b : Bool) -> BExp
 le : (a₁ : AExp) -> (a₂ : AExp) -> BExp 
 not : (b : BExp) -> BExp 
 and : (b₁ : BExp) -> (b₂ : BExp) -> BExp 


vars-bexp : (b : BExp) -> Store
vars-bexp (const b) = empty
vars-bexp (le a₁ a₂) = join (vars-aexp a₁) (vars-aexp a₂)
vars-bexp (not b) = (vars-bexp b) 
vars-bexp (and b b₁) = join (vars-bexp b) (vars-bexp b₁)

------------------------------------------------------------------------
-- Useful shortands for booleans
------------------------------------------------------------------------
eq : AExp -> AExp -> BExp
eq a₁ a₂ = and (not (le a₁ a₂)) (not (le a₂ a₁))

neq : AExp -> AExp -> BExp
neq a₁ a₂ = not (eq a₁ a₂)

geq : AExp -> AExp -> BExp
geq a₁ a₂ = not (le a₂ a₁)

gt : AExp -> AExp -> BExp
gt a₁ a₂ = and (geq a₁ a₂) (neq a₁ a₂)

or : BExp -> BExp -> BExp 
or b₁ b₂ = not (and (not b₁) (not b₂))

leq : AExp -> AExp -> BExp
leq a₁ a₂ = or (eq a₁ a₂) (le a₁ a₂)

------------------------------------------------------------------------
-- Properties of boolean expressions 
------------------------------------------------------------------------
module _ where
 open import Data.Maybe
 open import Data.Product
 open import Relation.Binary.PropositionalEquality
 --- 
 
 -- Subexpression relation
 data _⊆ᵇ_ : BExp ->  BExp -> Set where
  refl : ∀ (b : BExp)  -> b ⊆ᵇ b
  and-l : ∀ (b b₁ : BExp) -> b ⊆ᵇ (and b b₁) 
  and-r : ∀ (b b₁ : BExp) -> b₁ ⊆ᵇ (and b b₁)
  not : ∀ (b : BExp) -> b ⊆ᵇ (not b)
 
 data _⊆ᵃᵇ_ : AExp ->  BExp -> Set where
  le-l : ∀ (a a₁ : AExp) -> a ⊆ᵃᵇ (le a a₁)
  le-r : ∀ (a a₁ : AExp) -> a₁ ⊆ᵃᵇ (le a a₁)
 
 ⊆ᵇ-⊆ᵤ : ∀ (b₁ b₂ : BExp) -> (b₁⊆b₂ : b₁ ⊆ᵇ b₂) -> (vars-bexp b₁) ⊆ᵤ (vars-bexp b₂)
 ⊆ᵇ-⊆ᵤ b₁ .b₁ (refl .b₁) id x = x
 ⊆ᵇ-⊆ᵤ b₁ .(and b₁ b₂) (and-l .b₁ b₂) id x with (vars-bexp b₁) | (vars-bexp b₂)
 ... | s | s' with (s id) | (s' id)
 ... | just x₁ | just x₂ = x₁ , refl
 ... | just x₁ | nothing = x₁ , refl
 ⊆ᵇ-⊆ᵤ b₁ .(and b b₁) (and-r b .b₁) id x 
  with (vars-bexp (and b b₁)) | (vars-bexp b₁) | (vars-bexp b)
 ... | s | s' | s₁' with (s id) | (s' id) in eq-s-id | (s₁' id) 
 ... | just x₁ | just x₂ | just x₃ = x₃ , refl
 ... | just x₁ | just x₂ | nothing = x₂ , eq-s-id
 ... | nothing | just x₁ | just x₂ = x₂ , refl
 ... | nothing | just x₁ | nothing = x₁ , eq-s-id
 ⊆ᵇ-⊆ᵤ b₁ .(not b₁) (not .b₁) id x = x

 ⊆ᵃᵇ-⊆ᵤ : ∀ (a : AExp) (b : BExp) -> (a⊆b : a ⊆ᵃᵇ b) -> (vars-aexp a) ⊆ᵤ (vars-bexp b)
 ⊆ᵃᵇ-⊆ᵤ a .(le a a₁) (le-l .a a₁) id x with (vars-aexp a) 
 ... | s with (s id)
 ... | just x₁ = x₁ , refl
 ⊆ᵃᵇ-⊆ᵤ a .(le a₁ a) (le-r a₁ .a) id x with (vars-aexp a₁) | (vars-aexp a)
 ... | s₁ | s with (s₁ id) | (s id) in eq-sid
 ... | just x₁ | just x₂ = x₁ , refl
 ... | nothing | just x₁ = x₁ , eq-sid
