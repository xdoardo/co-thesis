------------------------------------------------------------------------
-- Compilation of arithmetic expressions from IMP to Stack
------------------------------------------------------------------------
module Stack.Imp.Compile.Arith where 

open import Imp.Syntax
open import Stack.Syntax
open import Data.List renaming (_∷_ to _::_)
---

comp-aexp : (a : AExp) -> Code
comp-aexp (const x) = (iconst x) :: [] 
comp-aexp (var x) = (ivar x) :: []
comp-aexp (plus a a₁) = (comp-aexp a) ++ (comp-aexp a₁) ++ iadd :: []
comp-aexp (minus a a₁) = (comp-aexp a) ++ (comp-aexp a₁) ++ iopp :: iadd :: []
comp-aexp (times a a₁) = (comp-aexp a) ++ (comp-aexp a₁) ++ imul :: []
comp-aexp (div a a₁) = (comp-aexp a) ++ (comp-aexp a₁) ++ idiv :: []

------------------------------------------------------------------------
-- Lemmas and examples 
------------------------------------------------------------------------

module _ where 
