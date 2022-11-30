------------------------------------------------------------------------
-- Values for imp 
-----------------------------------------------------------------------
module Imp.Syntax.Value where 


open import Data.Bool
open import Data.Maybe
open import Data.Integer as Int using (ℤ)
open import Data.String as String using (String ; _==_)
-- 

mutual 
 data State : Set where 
  [] : State 
  [_=>_::_] : String -> ℤ -> State -> State
  _::_ : State -> State -> State

 data Value : Set where
  v-lit : ℤ -> State -> Value

lookup : State -> String -> Maybe ℤ
lookup [] x₁ = nothing
lookup [ x => val :: x₃ ] x₁ = if (x == x₁) then (just val) else (lookup x₃ x₁)
lookup (x :: x₂) x₁ = let
  mv₁ = lookup x x₁
  mv₂ = lookup x₂ x₁
 in if (is-just mv₁) then mv₁ else mv₂
