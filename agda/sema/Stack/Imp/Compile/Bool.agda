------------------------------------------------------------------------
-- Compilation of arithmetic expressions from IMP to Stack
------------------------------------------------------------------------
module Stack.Imp.Compile.Bool where 

open import Data.Bool
open import Data.Integer
open import Stack.Syntax
open import Stack.Imp.Compile.Arith
open import Data.List renaming (_∷_ to _::_)
open import Imp.Syntax hiding (if_then_else_)
---


-- For Boolean expressions `b`, we could produce code that deposits `1` or `0` at the
-- top of the stack, depending on whether `b` is true or false. The compiled code
-- for `ifelse` and `while` commands would, then, perform an `ibeq` jump
-- conditional on this `0` or `1` value. However, it is simpler and more efficient to
-- compile a Boolean expression `b` to a piece of code that directly jumps `d₁` or
-- `d₂` instructions forward, depending on whether `b` is true or false. The actual
-- value of `b` is never computed as an integer, and the stack is unchanged. 

comp-bexp : (b : BExp) -> (d₁ d₂ : ℤ) -> Code
comp-bexp true d₁ d₂ = if ((d₁ ≤ᵇ 0ℤ) ∧ ( 0ℤ ≤ᵇ d₁)) then [] else (ibranch d₁) :: []
comp-bexp false d₁ d₂ = if ((d₂ ≤ᵇ 0ℤ) ∧ ( 0ℤ ≤ᵇ d₂)) then [] else (ibranch d₂) :: []
comp-bexp (eq a₁ a₂) d₁ d₂ = comp-aexp a₁ ++ comp-aexp a₂ ++ (ibeq d₁ d₂) :: []
comp-bexp (leq a₁ a₂) d₁ d₂ = comp-aexp a₁ ++ comp-aexp a₂ ++ (ibleq d₁ d₂) :: []
comp-bexp (BExp.not b) d₁ d₂ = comp-bexp b d₂ d₁ 
comp-bexp (BExp.and b b₁) d₁ d₂ = let  
  code₂ = comp-bexp b₁ d₁ d₂ 
  code₁ = comp-bexp b 0ℤ (+ codelen code₂ + d₂) 
 in code₁ ++ code₂

------------------------------------------------------------------------
-- Lemmas and examples 
------------------------------------------------------------------------

module _ where 
