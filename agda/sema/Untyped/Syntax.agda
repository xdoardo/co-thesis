------------------------------------------------------------------------
-- The syntax of the untyped λ-calculus with constants
-----------------------------------------------------------------------
module Untyped.Syntax where

open import Data.Nat
open import Data.Fin using (Fin ; #_ ; zero ; suc)
open import Relation.Nullary.Decidable
---

-- Terms. Variables are represented using de Brujin indices. 
data Tm (n : ℕ) : Set where
  con : (i : ℕ) → Tm n
  var : (x : Fin n) → Tm n
  ƛ : (t : Tm (suc n)) → Tm n
  _∙_ : (t₁ t₂ : Tm n) → Tm n

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


-- Convenient helper.
vr : ∀ m {n} {m<n : True (suc m ≤? n)} → Tm n
vr _ {m<n = m<n} = var (#_ _ {m<n = m<n})


------------------------------------------------------------------------
-- Example

-- A non-terminating term.

ω : Tm 0
ω = ƛ (vr 0 ∙ vr 0)

Ω : Tm 0
Ω = ω ∙ ω
