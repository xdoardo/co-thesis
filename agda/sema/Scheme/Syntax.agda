------------------------------------------------------------------------
-- The syntax of the Lisp dialect Scheme 
-----------------------------------------------------------------------
module Scheme.Syntax where

open import Size
open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Vec hiding (lookup)
open import Data.Maybe
open import Data.String
open import Data.Integer hiding (_>_)
open import Agda.Builtin.Float

data Atom : Set where 
  symbol : String -> Atom
  int : ℕ -> Atom 
  float : Float -> Atom

data Exp {i : Size}: Set where 
  atom : Atom -> Exp {i}
  list : ∀ {n : ℕ} {j : Size< i} -> {n > 0} -> Vec (Exp {j}) n  -> Exp {i}

data Env : Set where 
  ε : Env 
  [_|->_,_] : String -> Exp -> Env -> Env


env_from_prods : ∀ {n} -> Vec (String × Exp) n -> Env
env_from_prods [] = ε 
env_from_prods ((str , exp) ∷ e) = [ str |-> exp , (env_from_prods e) ]

lookup : String -> Env -> Maybe (Exp)
lookup s ε = nothing 
lookup s [ s₁ |-> e , Γ ] = if s == s₁ then just e else (lookup s Γ)
