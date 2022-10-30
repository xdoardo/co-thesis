------------------------------------------------------------------------
-- Functional semantics for an untyped λ-calculus with constants
------------------------------------------------------------------------
open import Lambda.Syntax
open import Data.Maybe as Maybe
open import DelayMonad
open import Category.Monad 
open import Function
open import Data.Vec

module Lambda.FunctionalSemantics where 

PartialityFunctor : RawMonad (Delay ∘ Maybe)
PartialityFunctor = Maybe DelayMonad.delayMonad

mutual 

  ⟦_⟧ : ∀ {n} → Tm n → Env n → ∞Delay (Maybe Value)
  ⟦ con i ⟧   ρ = (RawMonad PartialityFunctor).return (con i)
  ⟦ var x ⟧   ρ = (RawMonad PartialityFunctor).return (lookup x ρ)
  ⟦ ƛ t ⟧     ρ = (RawMonad PartialityFunctor).return (ƛ t ρ)
  ⟦ t₁ · t₂ ⟧ ρ = ⟦ t₁ ⟧ ρ >>= λ v₁ →
                  ⟦ t₂ ⟧ ρ >>= λ v₂ →
                  v₁ ∙ v₂

  _∙_ : Value → Value → ∞Delay (Maybe Value)
  con i  ∙ v₂ = fail
  ƛ t₁ ρ ∙ v₂ = later (♯ (⟦ t₁ ⟧ (v₂ ∷ ρ)))
