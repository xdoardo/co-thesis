----------------------------------------------------------------------------------------------
-- Properties of (or induced by) the type system for the λ calculus with constants
----------------------------------------------------------------------------------------------
module Lambda.Types.Properties where

open import Size 
open import Data.Nat 
open import Lambda.Syntax 
open import Lambda.Types.Core
open import Codata.Sized.Thunk
open import Data.Vec renaming (_∷_ to _::_)
-- 

module HasType where
 data _⊢_∈_ {n} (Γ : Ctxt n {∞}) : Tm n → Ty ∞ → Set where
   con : ∀ {i} → Γ ⊢ t-con i ∈ ⋆
   var : ∀ {x} → Γ ⊢ t-var x ∈ (lookup Γ x)
   lam : ∀ {t σ τ} (t∈ : (force σ :: Γ) ⊢ t ∈ (force τ)) -> Γ ⊢ t-lam t ∈ (σ => τ)
   app : ∀ {t₁ t₂ σ τ} (t₁∈ : Γ ⊢ t₁ ∈ (σ => τ)) (t₂∈ : Γ ⊢ t₂ ∈ (force σ)) -> 
          Γ ⊢ t-app t₁  t₂ ∈ (force τ)
 
 --- Examples 
 module _ where
  -- An infinite type.
  ss : ∀ {i} -> Ty i 
  ss = (λ where .force -> ss) => (λ where .force -> ss)
  
  Ω-well-typed : [] ⊢ Ω ∈ ss
  Ω-well-typed = app {σ = λ where .force -> ss} {τ = λ where .force -> ss} 
                  (lam (app var var)) (lam (app var var))
 
-- Typing predicates for values and computations.
module WellFounded where

  open HasType
  open import Data.Fin
  open import Data.Maybe
  open import Relation.Nullary
  open import Codata.Sized.Partial
  open import Data.Maybe.Relation.Unary.Any
  open import Codata.Sized.Delay.Relation.Unary.All
  open import Codata.Sized.Partial.Bisimilarity.Weak
  ---

  --  WFᵥ σ v means that the value v is well-formed with respect to the type σ.
  mutual 
    data WFᵥ {i} : Ty i -> Value -> Set where 
      -- constant values have type ⋆
      con : ∀ {n} -> WFᵥ ⋆ (v-con n) 
      -- if t has type τ 
      lam : ∀ {n Γ σ τ} {t : Tm (suc n)} {ρ}
             (t∈ : ((force σ) :: Γ) ⊢ t ∈ (force τ)) (ρ-wf : WFₑ Γ ρ) ->
              WFᵥ (σ => τ) (v-lam t ρ)

    data WFₑ  : ∀ {n} -> Ctxt n -> Env n -> Set where 
      []   : WFₑ [] [] -- empty environment 
      _::_ : ∀ {n} {Γ : Ctxt n} {ρ σ v}
              (v-wf : WFᵥ σ v) -- v is a well formed value w.r.t. the type σ 
              (ρ-wf : WFₑ Γ ρ) -> -- ρ is a well formed environment w.r.t. the context Γ
               -- adding σ to Γ and v to ρ keeps well-formedness (de facto giving the type σ to v)
               WFₑ (σ :: Γ) (v :: ρ) 

  -- Variables pointing into a well-formed environment refer to
  -- well-formed values.
  lookup-wf : ∀ {n Γ ρ} (nf : Fin n) -> WFₑ Γ ρ -> 
               WFᵥ (lookup Γ nf) (lookup ρ nf)
  lookup-wf zero (v :: ρ) = v
  lookup-wf (suc nf) (v :: ρ) = lookup-wf nf ρ

  -- If we can prove All (WF-MV σ) x, then x does not "go wrong".
  does-not-go-wrong : ∀ {i σ v} -> All (Any (WFᵥ σ)) ∞ v -> ¬ (i ⊢ v ≈ fail)
  does-not-go-wrong (now ()) nown
  does-not-go-wrong (later wf) (laterₗ bisim) = does-not-go-wrong (force wf) bisim
