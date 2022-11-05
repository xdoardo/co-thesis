------------------------------------------------------------------------
-- Functional semantics for an untyped λ-calculus with constants
------------------------------------------------------------------------

open import Category.Monad
open import Function 
open import Lambda.Syntax
open import Monad.PartialityMonad
open import Monad.SizedMaybeMonad using (Maybe)
open import Monad.DelayMonad using (Delay; ∞Delay)
open import Data.Nat using(suc)
--- 

module Lambda.FunctionalSemantics where 

open RawMonad PartialityMonad 

fail : {A : Set} → Delay (Maybe A)
fail = Delay.now Maybe.nothing

mutual

  eval : ∀ { i n } -> Tm n -> Env n -> Delay {i} (Maybe Value)
  eval (con i) ρ = Delay.now (Maybe.just (con i))
  eval (var x) ρ = Delay.now (Maybe.just (lookup ρ x))
  eval (ƛ t) ρ =  Delay.now (Maybe.just (ƛ t ρ))
  eval (t ○ u) ρ = eval t ρ >>= λ f -> eval u ρ >>= λ v -> apply f v

  apply : ∀ {i} -> Value -> Value -> Delay {i} (Maybe Value)
  apply (con i) v = fail 
  apply (ƛ t ρ) v = Delay.later (beta t ρ v)
  
  beta : ∀ {i n} -> Tm (suc n) -> Env n -> Value -> ∞Delay {i} (Maybe Value)
  ∞Delay.force(beta t ρ v)  = eval t (v , ρ)
