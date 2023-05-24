------------------------------------------------------------------------
-- Boolean expressions of IMP
------------------------------------------------------------------------
module Imp.Syntax.Bool where 

open import Imp.Syntax.Arith
open import Imp.Syntax.Ident
open import Data.Bool hiding (not)
open import Data.List using (_∷_ ; _++_ ; List ; [] )
---

data BExp : Set where 
 const : (b : Bool) -> BExp
 le : (a₁ : AExp) -> (a₂ : AExp) -> BExp 
 not : (b : BExp) -> BExp 
 and : (b₁ : BExp) -> (b₂ : BExp) -> BExp 


vars-bexp : (b : BExp) -> List Ident
vars-bexp (const b) = []
vars-bexp (le a₁ a₂) = (vars-aexp a₁) ++ (vars-aexp a₂)
vars-bexp (not b) = (vars-bexp b) 
vars-bexp (and b b₁) = (vars-bexp b) ++ (vars-bexp b₁)

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
