---------------------------------------------------------------------------
-- Evaluation 
---------------------------------------------------------------------------

module Lambda.Eval where 


open import Category.Monad
open import Lambda.Context 
open import Lambda.Type 
open import Lambda.Term using (Tm ; Ne)
open import Lambda.Value using (Env ; Val ; lookup)
open import DelayMonad

open RawMonad delayMonad

mutual 
  eval : ∀ {i Γ Δ b} -> Tm Γ b -> Env Δ Γ -> Delay {i} (Val Δ b)
  eval (Tm.var x)   ρ = DelayMonad.Delay.now (lookup x ρ)
  eval (Tm.abs t)   ρ = DelayMonad.Delay.now (Val.lam t ρ)
  eval (Tm.app t u) ρ = eval t ρ DelayMonad.>>= λ f -> eval u ρ DelayMonad.>>= λ v -> apply f v

  apply : ∀ {i Δ a b} -> Val Δ (a => b) -> Val Δ a -> DelayMonad.Delay {i} (Val Δ b)
  apply (Val.ne w) v    = now (Val.ne (Ne.app w v))
  apply (Val.lam t ρ) v = later (beta t ρ v)

  beta : ∀ {i Γ Δ a b} -> Tm (Γ , a) b -> Env Δ Γ -> Val Δ a -> ∞Delay {i} (Val Δ b)
  ∞Delay.force (beta t ρ v) = eval t (Env._,_ ρ v)
