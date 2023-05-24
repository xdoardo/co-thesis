------------------------------------------------------------------------
-- Arithmetic expressions of Imp
------------------------------------------------------------------------
module Imp.Syntax.Arith where 

open import Data.List
open import Data.Integer using (ℤ)
open import Imp.Syntax.Ident using (Ident ; Store)
--- 

data AExp : Set where 
 const : (n : ℤ) -> AExp
 var   : (id : Ident) -> AExp 
 plus  : (a₁ : AExp) -> (a₂ : AExp) -> AExp

vars-aexp : (a : AExp) -> List Ident
vars-aexp (const n) = []
vars-aexp (var id) = id ∷ []
vars-aexp (plus a a₁) = (vars-aexp a) ++ (vars-aexp a₁)

------------------------------------------------------------------------
-- Properties of arithmetic expressions 
------------------------------------------------------------------------
