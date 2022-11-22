----------------------------------------------------------------------------------------------
-- Functional semantics in continuation passing style for the λ-calculus with constants
----------------------------------------------------------------------------------------------

module Lambda.Semantics.Continuation where 

open import Size
open import Lambda.Syntax
open import Data.Nat using (suc)
open import Data.Maybe using (Maybe)
open import Data.Vec renaming (_∷_ to _::_)
open import Codata.Sized.Delay using (Delay)
open import Codata.Sized.Thunk using (Thunk)
open import Codata.Sized.Partial using (fail ; never)
--- 

open Delay
open Thunk
open Maybe 
---

mutual

  evalₚ : ∀ { i n } -> Tm n -> Env n -> 
           (Value -> (Delay (Maybe Value) i)) -> Delay (Maybe Value) i
  evalₚ (t-con i) ρ k = k (v-con i) 
  evalₚ (t-var x) ρ k = k (lookup ρ x) 
  evalₚ (t-lam t) ρ k = k (v-lam t ρ) 
  evalₚ (t-app t₁ t₂) ρ k = evalₚ t₁ ρ (λ v₁ -> evalₚ t₂ ρ (λ v₂ -> applyₚ v₁ v₂ k)) 
  -- 			^^ Note, no bind here thanks to CPS

  applyₚ : ∀ {i} -> Value -> Value -> (Value -> (Delay (Maybe Value) i)) 
           -> Delay (Maybe Value) i
  applyₚ (v-con i) _ _ = fail
  applyₚ (v-lam t ρ) v k = later (betaₚ t ρ v k)
  
  betaₚ : ∀ {i n} -> Tm (suc n) -> Env n -> Value -> (Value -> (Delay (Maybe Value) i)) 
           ->  Thunk (Delay (Maybe Value)) i
  force(betaₚ t ρ v k)  = evalₚ t (v :: ρ) k

------------------------------------------------------------------------
-- Examples
module _ where 

  open import Function using (_∘_)
  open import Effect.Applicative
  open import Codata.Sized.Partial.Bisimilarity.Weak
  open import Codata.Sized.Partial.Effectful using (applicative)
  open RawApplicative {Agda.Primitive.lzero} {Agda.Primitive.lzero} applicative 

  -- Ω is weakly bisimilar to never.
  Ω-loopsₚ : ∀ {i} -> i ⊢ (evalₚ Ω [] (now ∘ just)) ≈ never
  Ω-loopsₚ = later (λ where .force -> Ω-loopsₚ) 
