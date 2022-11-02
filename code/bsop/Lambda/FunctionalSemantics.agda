------------------------------------------------------------------------
-- Functional semantics for an untyped λ-calculus with constants
------------------------------------------------------------------------

open import Category.Monad
open import Function 
open import Lambda.Syntax
open import Monad.PartialityMonad
open import Monad.DelayMonad using (Delay; ∞Delay)
open import Data.Maybe using (Maybe)
open import Data.Vec using (lookup; _∷_)
--- 

module Lambda.FunctionalSemantics where 
open RawMonad PartialityFunctor public

fail : {A : Set} → Delay (Maybe A)
fail = Delay.now Maybe.nothing

mutual

  ⟦_⟧ : ∀ {i n} → Tm n → Env n → Delay {i} (Maybe Value)
  ⟦ con i ⟧   ρ = return (con i)
  ⟦ var x ⟧   ρ = return (lookup ρ x)
  ⟦ ƛ t ⟧     ρ = return (ƛ t ρ)
  ⟦ t₁ · t₂ ⟧ ρ = ⟦ t₁ ⟧ ρ >>= λ v₁ →
                  ⟦ t₂ ⟧ ρ >>= λ v₂ →
                  v₁ ∙ v₂

  _∙_ : ∀ {i} -> Value → Value → Delay {i} (Maybe Value)
  con i  ∙ v₂ = fail
  ƛ t₁ ρ ∙ v₂ = ⟦ t₁ ⟧ (v₂ ∷ ρ)
