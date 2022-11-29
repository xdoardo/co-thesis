----------------------------------------------------------------------------------------------
-- Properties of the λ calculus with constants
----------------------------------------------------------------------------------------------

module Lambda.Properties where

open import Size 
open import Data.Nat
open import Data.Maybe
open import Lambda.Types
open import Lambda.Syntax
open import Codata.Sized.Thunk
open import Codata.Sized.Partial
open import Lambda.Types.Properties
open import Lambda.Semantics.Normal
open import Relation.Nullary using (¬_)
open import Data.Maybe.Relation.Unary.Any
open import Data.Vec renaming (_∷_ to _::_)
open import Codata.Sized.Partial.Relation.Unary.All
open import Codata.Sized.Partial.Bisimilarity.Weak
--

open HasType
open WellFounded
--

-- Computations resulting from evaluating well-typed terms in well-
-- formed environments are well-formed
mutual 
  eval-wf : ∀ {n Γ i} (t : Tm n) {σ} -> Γ ⊢ t ∈ σ -> ∀ {ρ} -> WFₑ Γ ρ -> 
             All (WFᵥ σ) i (eval t ρ)
  eval-wf (t-con i)    con           ρ-wf = now con
  eval-wf (t-var v)    var           ρ-wf = now (lookup-wf v ρ-wf)
  eval-wf (t-lam t)    (lam t-is-σ)  ρ-wf = now (lam t-is-σ ρ-wf)
  eval-wf {n} {Γ} {i} (t-app t₁ t₂) (app t₁∈ t₂∈) {ρ} ρ-wf =
    eval (t-app t₁ t₂) ρ ≡< ∙-comp t₁ t₂ i > 
     (
      (eval t₁ ρ) ⟦∙⟧ (eval t₂ ρ) ≡<(
       eval-wf t₁ t₁∈ ρ-wf >>=-cong 
          λ { .{_} (f-wf) -> eval-wf t₂ t₂∈ ρ-wf >>=-cong 
           λ { .{_} (v-wf) -> apply-wf f-wf v-wf }}
      )>
     ) where open Reasoning

  apply-wf :  ∀ {σ τ f v i} -> WFᵥ (σ => τ) f -> WFᵥ (force σ) v -> 
               All (WFᵥ (force τ)) i (apply f v) 
  apply-wf {σ} {τ} {v} {t} (lam t∈ ρ-wf) v-wf = 
    later λ where .force -> beta-wf {σ = σ} {τ = τ} v-wf ρ-wf t∈

  beta-wf : ∀ {n v i} {σ τ : Thunk (Ty) ∞} {f : Tm (suc n)} {Γ : Ctxt n} {ρ : Env n} -> 
             WFᵥ (force σ) v -> WFₑ Γ ρ -> ((force σ :: Γ) ⊢ f ∈ (force τ)) -> 
              All (WFᵥ (force τ)) i (beta f ρ v .force)
  beta-wf {n} {v} {i} {σ} {τ} {f} {Γ} {ρ} v-wf ρ-wf t∈ = eval-wf f t∈ (v-wf :: ρ-wf)

type-soundness : ∀ {t : Tm 0} {i} {σ} -> [] ⊢ t ∈ σ -> ¬ (i ⊢ (eval t []) ≈ fail)
type-soundness {t} t∈ = does-not-go-wrong (eval-wf t t∈ [])
