------------------------------------------------------------------------
-- An effectful view of Partial
------------------------------------------------------------------------

module Codata.Sized.Partial.Effectful where


open import Size
open import Function
open import Effect.Empty
open import Effect.Monad
open import Effect.Functor
open import Effect.Applicative
open import Codata.Sized.Partial
open import Data.Maybe using (Maybe)
open import Codata.Sized.Delay using (Delay)
---

open Delay
open Maybe 
--

functor : ∀ {i ℓ} → RawFunctor {ℓ} (λ A → Delay (Maybe A) i)
functor = record { _<$>_ = λ f → map f }

applicative : ∀ {i ℓ} → RawApplicative {ℓ} (λ A → Delay (Maybe A) i)
applicative = record
  { rawFunctor = functor
  ; pure = now ∘ just
  ; _<*>_  = λ df da → bind df (λ f → map f da)
  }

monad : ∀ {i ℓ} → RawMonad {ℓ} (λ A → Delay (Maybe A) i)
monad = record
  { rawApplicative = applicative
  ; _>>=_  = bind
  }
