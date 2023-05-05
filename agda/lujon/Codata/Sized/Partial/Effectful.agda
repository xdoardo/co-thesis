------------------------------------------------------------------------
-- An effectful view of Partial
------------------------------------------------------------------------

module Codata.Sized.Partial.Effectful where 

open import Size
open import Data.Nat
open import Effect.Empty
open import Effect.Monad
open import Effect.Functor
open import Effect.Applicative
open import Codata.Sized.Conat
open import Function hiding (force)
open import Data.Maybe using (Maybe)
open import Codata.Sized.Delay using (Delay) renaming (map to delayMap)
open import Codata.Sized.Thunk using (Thunk)
---

open Delay
open Thunk
open Maybe 
---

module _ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} where

 map : (A -> B) -> ∀ {i} -> Delay (Maybe A) i -> Delay (Maybe B) i
 map f (now (just x)) = now (just (f x))
 map f (now nothing) = now nothing 
 map f (later x) = later (λ where .force -> map f (x .force))  

 bind : ∀ {i} -> Delay {ℓ} (Maybe A) i -> (A -> Delay {ℓ′}(Maybe B) i) -> Delay {ℓ′} (Maybe B) i
 bind (now (just x)) f = f x
 bind (now nothing) f = now nothing 
 bind (later x) f = later (λ where .force -> bind (x .force) f) 


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
