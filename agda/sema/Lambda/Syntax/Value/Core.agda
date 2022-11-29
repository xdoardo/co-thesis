------------------------------------------------------------------------
-- Values and environments for the λ-calculus
-----------------------------------------------------------------------
module Lambda.Syntax.Value.Core where

open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Lambda.Syntax.Term.Core
-- 

mutual 
 -- Lambdas are represented using closures, so values do not contain any free
 -- variables.
 data Value : Set where
   v-con : (i : ℕ) → Value
   v-lam : ∀ {n} (t : Tm (suc n)) (ρ : Env n) → Value

 Env : ℕ → Set
 Env n = Vec Value n  
