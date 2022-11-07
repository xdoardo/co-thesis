------------------------------------------------------------------------
-- Functional semantics for an untyped λ-calculus with constants
------------------------------------------------------------------------

module Lambda.FunctionalSemantics where 

open import Category.Monad
open import Function 
open import Lambda.Syntax
open import Data.Partial
open import Data.Maybe using (Maybe)
open import Agda.Builtin.Size
open import Data.Delay using (Delay; ∞Delay)
open import Data.Nat using (suc)
open import Data.Fin
--- 

open Delay
open Maybe 
open ∞Delay
---

mutual

  eval : ∀ { i n } -> Tm n -> Env n -> Delay {i} (Maybe Value)
  eval (con i) ρ = now (just (con i))
  eval (var x) ρ = now (just (lookup ρ x))
  eval (ƛ t) ρ =  now (just (ƛᵥ t ρ))
  eval (t ○ u) ρ = eval t ρ >>= λ f -> eval u ρ >>= λ v -> apply f v

  apply : ∀ {i} -> Value -> Value -> Delay {i} (Maybe Value)
  apply (con i) v = now nothing
  apply (ƛᵥ t ρ) v = later (beta t ρ v)
  
  beta : ∀ {i n} -> Tm (suc n) -> Env n -> Value -> ∞Delay {i} (Maybe Value)
  ∞Delay.force(beta t ρ v)  = eval t (v , ρ)



open import Agda.Builtin.Equality 

-- A constant is evaluated to that constant wrapped in (now ∘ just)
_ : eval (con 1) ε ≡ (now (just (Value.con 1)))
_ = refl

-- An application where the lhs is not an abstraction is an error (now nothing)
_ : eval ((con 1) ○ (con 1)) ε ≡ (now nothing)
_ = refl

-- A variable in scope is evaluated to its value
_ : eval (var Fin.zero) (Value.con 1 , ε) ≡ now (just (Value.con 1))
_ = refl

-- An abstraction is evaluated to an abstraction value
_ : eval (ƛ (var (Fin.suc Fin.zero))) (Value.con 1 , ε) ≡ now (just (ƛᵥ (var (Fin.suc Fin.zero)) (Value.con 1 , ε)))
_ = refl

