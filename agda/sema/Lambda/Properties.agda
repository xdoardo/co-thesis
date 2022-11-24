----------------------------------------------------------------------------------------------
-- Properties of the λ calculus with constants
----------------------------------------------------------------------------------------------

module Lambda.Properties where

open import Size 
open import Data.Vec
open import Data.Maybe
open import Lambda.Types
open import Lambda.Syntax
open import Codata.Sized.Thunk
open import Codata.Sized.Partial
open import Lambda.Types.Properties
open import Lambda.Semantics.Normal
open import Data.Maybe.Relation.Unary.Any
open import Codata.Sized.Partial.Relation.Unary.All
--

open HasType
open WellFounded
--

-- Computations resulting from evaluating well-typed terms in well-
-- formed environments are well-formed
mutual 
  eval-wf : ∀ {n Γ i} (t : Tm n) {σ} → Γ ⊢ t ∈ σ → ∀ {ρ} → WFₑ Γ ρ → All (WFᵥ σ) i (eval t ρ)
  eval-wf (t-con i)    con           ρ-wf = now con
  eval-wf (t-var v)    var           ρ-wf = now (lookup-wf v ρ-wf)
  eval-wf (t-lam t)    (lam t-is-σ)  ρ-wf = now (lam t-is-σ ρ-wf)
  eval-wf (t-app t t₁) (app x x₁)    ρ-wf = ? 
