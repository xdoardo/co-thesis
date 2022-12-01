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

 data Value : Set where
  v-lit : ℤ -> State -> Value
  v-empty : State -> Value


_::_ : State -> State -> State
[] :: x₁ = x₁ 
[ x => x₂ :: x₃ ] :: x₁ = [ x => x₂ :: (x₃ :: x₁)] 

lookup : State -> String -> Maybe ℤ
lookup [] x₁ = nothing
lookup [ x => val :: x₃ ] x₁ = if (x == x₁) then (just val) else (lookup x₃ x₁)

get-state : Value -> State
get-state (v-lit _ ρ) = ρ 
get-state (v-empty ρ) = ρ 
