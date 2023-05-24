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

-- Subexpression relation
data _⊆ᵇ_ : {A : Set} -> A -> BExp -> Set where
 refl : ∀ (b : BExp)  -> b ⊆ᵇ b
 le-l : ∀ (a a₁ : AExp) -> a ⊆ᵇ (le a a₁)
 le-r : ∀ (a a₁ : AExp) -> a₁ ⊆ᵇ (le a a₁)
 and-l : ∀ (b b₁ : BExp) -> b ⊆ᵇ (and b b₁) 
 and-r : ∀ (b b₁ : BExp) -> b₁ ⊆ᵇ (and b b₁)
 not : ∀ (b : BExp) -> b ⊆ᵇ (not b)
