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

Ctxt : ℕ -> {Size} → Set
Ctxt n {i} = Vec (Ty i) n

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
 
module WellFounded where
  open HasType
  open import Data.Fin
  open import Data.Maybe
  open import Relation.Nullary
  open import Codata.Sized.Partial
  open import Data.Maybe.Relation.Unary.Any
  open import Codata.Sized.Delay.Relation.Unary.All
  open import Codata.Sized.Partial.Bisimilarity.Weak

  mutual 
    data WFᵥ {i} : Ty i -> Value -> Set where 
      con : ∀ {n} -> WFᵥ ⋆ (v-con n)
      lam : ∀ {n σ t τ ρ} {Γ : Ctxt n} -> ((force σ) :: Γ) ⊢ t ∈ (force τ) -> 
             WFₑ Γ ρ -> WFᵥ (σ => τ) (v-lam t ρ)

    data WFₑ  : {n : ℕ} -> Ctxt n -> Env n -> Set where 
      []   : WFₑ [] []
      _::_ : ∀ {σ v n'} {Γ : Ctxt n'} {ρ : Env n'} -> WFᵥ σ v -> WFₑ Γ ρ -> 
              WFₑ (σ :: Γ) ( v :: ρ )

  -- Maybe.Any: 
  -- data Any {a p} {A : Set a} (P : Pred A p) : Pred (Maybe A) (a ⊔ p) where
  --   just : ∀ {x} → P x → Any P (just x)
  -- For a given P and x, if P x, then Any P x -> x != nothing

  WF-MV : ∀ {i} -> Ty i → Maybe Value → Set
  WF-MV σ = Any (WFᵥ σ)

  -- Variables pointing into a well-formed environment refer to
  -- well-formed values.
  lookup-wf : ∀ {n Γ ρ} (x : Fin n) → WFₑ Γ ρ → WFᵥ (lookup Γ x) (lookup ρ x)
  lookup-wf zero (x :: wfv) = x
  lookup-wf (suc wfe) (x :: wfv) = lookup-wf wfe wfv
  
  -- If we can prove All (WF-MV σ) x, then x does not "go wrong".
  does-not-go-wrong : ∀ {i σ x} → All (WF-MV σ) ∞ x → ¬ (i ⊢ x ≈ fail)
  does-not-go-wrong (now ()) nown
  does-not-go-wrong {i} (later x₁) (laterₗ x) = does-not-go-wrong (force x₁) x
