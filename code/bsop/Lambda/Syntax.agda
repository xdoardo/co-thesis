------------------------------------------------------------------------
-- The syntax of the untyped λ-calculus with constants
-----------------------------------------------------------------------
module Lambda.Syntax where

open import Data.Nat
open import Data.Fin
open import Data.Vec

-- Terms

-- Variables are represented using de Bruijn indices.
data Tm (n : ℕ) : Set where
  con : (i : ℕ) → Tm n
  var : (x : Fin n) → Tm n
  ƛ   : (t : Tm (suc n)) → Tm n
  _·_ : (t₁ t₂ : Tm n) → Tm n

mutual 
  -- Environments.
  Env : ℕ → Set
  Env n = Vec Value n
  
  -- Values. Lambdas are represented using closures, so values do
  -- not contain any free variables.
  data Value : Set where
    con : (i : ℕ) → Value
    ƛ   : ∀ {n} (t : Tm (suc n)) (ρ : Env n) → Value
