----------------------------------------------------------------------------------------------
-- Type system for the λ calculus with constants
----------------------------------------------------------------------------------------------
module Lambda.Types where 

open import Size
open import Data.Nat 
open import Data.Product
open import Relation.Binary
open import Codata.Sized.Thunk
open import Data.Fin using (Fin)
open import Lambda.Syntax hiding (lookup)
open import Data.Vec renaming (_∷_ to _::_)


data Ty : Size -> Set where 
  * : ∀ {i} -> Ty i
  _=>_ : ∀ {i} -> Thunk Ty i -> Thunk Ty i -> Ty i


data Bisim (i : Size) : Ty ∞ -> Ty ∞ -> Set where 
  ≈-* : Bisim i (*) (*)
  ≈-=> : ∀ {t1 t2 t3 t4} -> Thunk^R Bisim i t1 t3 -> 
             Thunk^R Bisim i t2 t4 -> Bisim i (t1 => t2) (t3 => t4)

reflexive : ∀ {i} → Reflexive (Bisim i)
reflexive {i} {*} = ≈-*
reflexive {i} {x => x₁} = ≈-=> (λ where .force -> reflexive) (λ where .force -> reflexive)

Ctxt : ℕ -> {Size} → Set
Ctxt n {i} = Vec (Ty i) n

data _⊢_∈_ {n} (Γ : Ctxt n {∞}) : Tm n → Ty ∞ → Set where
  con : ∀ {i} → Γ ⊢ con i ∈ *
  var : ∀ {x} → Γ ⊢ var x ∈ lookup Γ x
  lam : ∀ {t σ τ} (t∈ : (force σ :: Γ) ⊢ t ∈ (force τ)) -> Γ ⊢ ƛ t ∈ (σ => τ)
  app : ∀ {t₁ t₂ σ τ} (t₁∈ : Γ ⊢ t₁ ∈ (σ => τ)) (t₂∈ : Γ ⊢ t₂ ∈ (force σ)) → Γ ⊢ t₁ ∙ t₂ ∈ (force τ)


-- An infinite type.
ss : ∀ {i} -> Ty i 
ss = (λ where .force -> ss) => (λ where .force -> ss)

Ω-well-typed : [] ⊢ Ω ∈ ss
Ω-well-typed = app {σ = λ where .force -> ss} {τ = λ where .force -> ss} (lam (app var var)) (lam (app var var))
