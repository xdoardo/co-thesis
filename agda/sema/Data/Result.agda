module Data.Result where 

open import Data.String
open import Effect.Empty
open import Effect.Monad
open import Effect.Functor
open import Effect.Applicative
--

data Result {a} {A : Set a} : Set a where
  Ok : A -> Result
  Err : String -> Result

------------------------------------------------------------------------
-- An effectful view on Result
------------------------------------------------------------------------
module _ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} where

  map : (A -> B) -> Result {ℓ} {A} -> Result {ℓ′} {B}
  map f (Ok x₁) = Ok (f x₁)
  map f (Err x₁) = Err x₁

  bind : Result {ℓ} {A} -> (A -> Result {ℓ′} {B}) -> Result {ℓ′} {B}
  bind (Ok x) f = f x
  bind (Err x) f = Err x
 

functor : ∀ {ℓ} → RawFunctor {ℓ} (λ A → Result {ℓ} {A})
functor = record { _<$>_ = λ f → map f }

applicative : ∀ {ℓ} → RawApplicative {ℓ} (λ A → Result {ℓ} {A})
applicative = record
  { rawFunctor = functor
  ; pure = Ok 
  ; _<*>_  = λ df da → bind df (λ f → map f da)
  }

monad : ∀ {ℓ} → RawMonad {ℓ} (λ A → Result {ℓ} {A})
monad = record
  { rawApplicative = applicative
  ; _>>=_  = bind
  }
