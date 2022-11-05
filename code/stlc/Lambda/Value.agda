---------------------------------------------------------------------------
-- Values and environments 
---------------------------------------------------------------------------

module Lambda.Value where 

open import Lambda.Context 
open import Lambda.Type 
open import Lambda.Term

mutual
  data Val (Δ : Ctx) : (a : Ty) → Set where
    ne : ∀{a} (w : Ne Val Δ a) → Val Δ a
    lam : ∀{Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) → Val Δ (a => b)
  
  data Env (Δ : Ctx) : (Γ : Ctx) → Set where
    ε : Env Δ ε
    _,_ : ∀ {Γ a} (ρ : Env Δ Γ) (v : Val Δ a) → Env Δ (Γ , a)

lookup : ∀ {Γ Δ a} → Var Γ a → Env Δ Γ → Val Δ a
lookup zero (ρ , v) = v
lookup (suc x) (ρ , v) = lookup x ρ

