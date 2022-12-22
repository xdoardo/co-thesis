------------------------------------------------------------------------
-- Arithmetic terms of IMP
------------------------------------------------------------------------
module Imp.Syntax.Arith where 

open import Imp.Syntax.Ident
open import Data.Integer using (ℤ)
--- 

data AExp : Set where 
 const : ℤ -> AExp
 var   : Ident -> AExp 
 plus  : (a₁ : AExp) -> (a₂ : AExp) -> AExp
 minus : (a₁ : AExp) -> (a₂ : AExp) -> AExp
 times : (a₁ : AExp) -> (a₂ : AExp) -> AExp
 div   : (a₁ : AExp) -> (a₂ : AExp) -> AExp
