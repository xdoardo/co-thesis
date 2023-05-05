------------------------------------------------------------------------
-- Boolean expressions of IMP
------------------------------------------------------------------------
module Imp.Syntax.Bool where 

open import Imp.Syntax.Arith
open import Data.Bool hiding (not)
---

data BExp : Set where 
 true : BExp 
 false : BExp 
 eq leq : (a₁ : AExp) -> (a₂ : AExp) -> BExp 
 not : (b : BExp) -> BExp 
 and : (b₁ : BExp) -> (b₂ : BExp) -> BExp 


neq : AExp -> AExp -> BExp
neq a₁ a₂ = not (eq a₁ a₂)

geq : AExp -> AExp -> BExp
geq a₁ a₂ = leq a₂ a₁

gt : AExp -> AExp -> BExp
gt a₁ a₂ = not (leq a₁ a₂)

lt : AExp -> AExp -> BExp
lt a₁ a₂ = gt a₂ a₁

or : BExp -> BExp -> BExp 
or b₁ b₂ = not (and (not b₁) (not b₂))
