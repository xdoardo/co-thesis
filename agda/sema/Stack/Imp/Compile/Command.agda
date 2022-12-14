------------------------------------------------------------------------
-- Compilation of commands from IMP to Stack
------------------------------------------------------------------------
module Stack.Imp.Compile.Command where 

open import Data.Nat using () renaming (_+_ to _+n_)
open import Imp.Syntax
open import Data.Integer
open import Stack.Syntax
open import Stack.Imp.Compile.Bool
open import Stack.Imp.Compile.Arith
open import Data.List renaming (_∷_ to _::_)
---

comp-com : (c : Command) -> Code
comp-com skip = [] 
comp-com (assign id a) = comp-aexp a ++ (isetvar id) :: []
comp-com (seq c c₁) = comp-com c ++ comp-com c₁ 
comp-com (ifelse b c c₁) = let 
  code-true = comp-com c
  code-false = comp-com c₁ 
 in comp-bexp b 0ℤ (+ (codelen code-true) + (+ 1)) ++ code-true 
   ++ (ibranch (+ codelen code-false)) :: code-false
comp-com (while b c) = let 
  code-body = comp-com c 
  code-test = comp-bexp b 0ℤ (+ (codelen code-body) + (+ 1))
 in code-test ++ code-body 
  ++ ibranch (- + (codelen code-test +n codelen code-body +n 1)) :: []


------------------------------------------------------------------------
-- Lemmas and examples 
------------------------------------------------------------------------

module _ where 
