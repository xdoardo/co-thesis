------------------------------------------------------------------------
-- Functional semantics for an untyped λ-calculus with constants
------------------------------------------------------------------------

module Lambda.Semantics where 

open import Lambda.Syntax
open import Data.Maybe using (Maybe)
open import Codata.Sized.Delay using (Delay)
open import Codata.Sized.Thunk using (Thunk)
open import Data.Nat using (suc)
open import Partial.Bind
--- 

open Delay
open Thunk
open Maybe 
---

mutual

  eval : ∀ { i n } -> Tm n -> Env n -> Delay (Maybe Value) i
  eval (con i) ρ = now (just (con i))
  eval (var x) ρ = now (just (lookup ρ x))
  eval (ƛ t) ρ =  now (just (ƛᵥ t ρ))
  eval (t ○ u) ρ = eval t ρ >>= λ f -> eval u ρ >>= λ v -> apply f v

  apply : ∀ {i} -> Value -> Value -> Delay (Maybe Value) i
  apply (con i) v = now nothing
  apply (ƛᵥ t ρ) v = later (beta t ρ v)
  
  beta : ∀ {i n} -> Tm (suc n) -> Env n -> Value -> Thunk (Delay (Maybe Value)) i
  force(beta t ρ v)  = eval t (v , ρ)