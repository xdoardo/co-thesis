------------------------------------------------------------------------
-- The syntax of the untyped λ-calculus with constants
-----------------------------------------------------------------------
module Lambda.Syntax where

open import Data.Nat
open import Data.Fin
---

-- Terms. Variables are represented using de Brujin indices. 
data Tm (n : ℕ) : Set where
  con : (i : ℕ) → Tm n
  var : (x : Fin n) → Tm n
  ƛ : (t : Tm (suc n)) → Tm n
  _○_ : (t₁ t₂ : Tm n) → Tm n

mutual 
  -- Environments.
  data Env : ℕ -> Set where 
    ε   : Env zero
    _,_ : {n : ℕ} -> Value -> Env n -> Env (suc n)
     
  -- Values. Lambdas are represented using closures, so values do
  -- not contain any free variables.
  data Value : Set where
    con : (i : ℕ) → Value
    ƛᵥ : ∀ {n} (t : Tm (suc n)) (ρ : Env n) → Value

lookup : ∀ {n : ℕ } -> Env n -> Fin n -> Value 
lookup (x , xs) zero    = x
lookup (x , xs) (suc i) = lookup xs i
