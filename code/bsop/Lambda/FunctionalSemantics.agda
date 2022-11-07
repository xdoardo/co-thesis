------------------------------------------------------------------------
-- Functional semantics for an untyped λ-calculus with constants
------------------------------------------------------------------------

module Lambda.FunctionalSemantics where 

open import Category.Monad
open import Function 
open import Lambda.Syntax
open import Monad.PartialityMonad
open import Monad.SizedMaybeMonad using (Maybe)
open import Agda.Builtin.Size
open import Monad.DelayMonad using (Delay; ∞Delay)
open import Data.Nat using (suc)
--- 

open Delay
open Maybe 
---

mutual

  eval : ∀ { i n } -> Tm n -> Env n -> Delay i (Maybe i Value)
  eval (con i) ρ = now (just (con i))
  eval (var x) ρ = now (just (lookup ρ x))
  eval (ƛ t) ρ =  now (just (ƛᵥ t ρ))
  eval (t ○ u) ρ = eval t ρ >>= λ f -> eval u ρ >>= λ v -> apply f v

  apply : ∀ {i} -> Value -> Value -> Delay i (Maybe i Value)
  apply (con i) v = now nothing
  apply (ƛᵥ t ρ) v = later (beta t ρ v)
  
  beta : ∀ {i n} -> Tm (suc n) -> Env n -> Value -> ∞Delay i (Maybe i Value)
  ∞Delay.force(beta t ρ v)  = eval t (v , ρ)
