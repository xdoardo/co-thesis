------------------------------------------------------------------------
-- Arithmetic expressions of Imp
------------------------------------------------------------------------
module Imp.Syntax.Arith where 

open import Imp.Syntax.Ident
open import Data.Integer using (ℤ)
--- 

data AExp : Set where 
 const : (n : ℤ) -> AExp
 var   : (id : Ident) -> AExp 
 plus  : (a₁ : AExp) -> (a₂ : AExp) -> AExp
