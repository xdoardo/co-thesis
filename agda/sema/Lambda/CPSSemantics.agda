----------------------------------------------------------------------------------------------
-- Functional semantics in continuation passing style for the λ-calculus with constants
----------------------------------------------------------------------------------------------

module Lambda.CPSSemantics where 

open import Size
open import Lambda.Syntax
open import Data.Nat using (suc)
open import Data.Maybe using (Maybe)
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
  evalₚ (con i) ρ k = k (con i) 
  evalₚ (var x) ρ k = k (lookup ρ x) 
  evalₚ (ƛ t) ρ k = k (ƛᵥ t ρ) 
  evalₚ (t₁ ∙ t₂) ρ k = evalₚ t₁ ρ (λ v₁ -> evalₚ t₂ ρ (λ v₂ -> apply v₁ v₂ k)) 
  -- 			^^ Note, no bind here thanks to CPS

  apply : ∀ {i} -> Value -> Value -> (Value -> (Delay (Maybe Value) i)) 
           -> Delay (Maybe Value) i
  apply (con i) _ _ = fail
  apply (ƛᵥ t ρ) v k = later (beta t ρ v k)
  
  beta : ∀ {i n} -> Tm (suc n) -> Env n -> Value -> (Value -> (Delay (Maybe Value) i)) 
           ->  Thunk (Delay (Maybe Value)) i
  force(beta t ρ v k)  = evalₚ t (v , ρ) k

------------------------------------------------------------------------
-- Examples
module _ where 

  open import Function using (_∘_)
  open import Effect.Applicative
  open import Codata.Sized.Partial.Bisimilarity.Weak
  open import Codata.Sized.Partial.Effectful using (applicative)
  open RawApplicative {Agda.Primitive.lzero} {Agda.Primitive.lzero} applicative 

  -- Ω is weakly bisimilar to never.
  Ω-loops : ∀ {i} -> i ⊢ (evalₚ Ω ε (now ∘ just)) ≈ never
  Ω-loops = later (λ where .force -> Ω-loops) 
