------------------------------------------------------------------------
-- An effectful view of FailingDelay 
------------------------------------------------------------------------

module Codata.Sized.FailingDelay.Effectful where 

open import Size
open import Data.Nat
open import Effect.Empty
open import Effect.Monad
open import Effect.Functor
open import Effect.Applicative
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

module _ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} where
 open import Codata.Sized.Delay.WeakBisimilarity 
 open import Codata.Sized.Delay.WeakBisimilarity.Relation.Binary.Equivalence 
  renaming (refl to prefl ; trans to ptrans ; sym to psym)

 bindx-≋ : ∀ {i} {x x' : Delay (Maybe A) ∞} {f : A -> Delay (Maybe B) ∞} (h-x : ∞ ⊢ x ≋ x') -> i ⊢ (bind x f) ≋ (bind x' f)
 bindx-≋ (now eq) rewrite eq = prefl
 bindx-≋ (laterᵣ h-x) = laterᵣ (bindx-≋ h-x) 
 bindx-≋ (laterₗ h-x) = laterₗ (bindx-≋ h-x) 
 bindx-≋ (later x) = later λ where .force -> bindx-≋ (force x)

 bindf-≋ : ∀ {i} {x : Delay (Maybe A) ∞} {f f' : A -> Delay (Maybe B) ∞} (h-f : ∀ v -> i ⊢ f v ≋ f' v) 
  -> i ⊢ (bind x f) ≋ (bind x f')
 bindf-≋ {_} {now (just x)} h-f = h-f x
 bindf-≋ {_} {now nothing} h-f = prefl 
 bindf-≋ {_} {later x} h-f = later λ where .force -> bindf-≋ {x = force x} h-f

 bind-≋ : ∀ {i} {x x' : Delay (Maybe A) ∞} {f f' : A -> Delay (Maybe B) ∞} (h-x : ∞ ⊢ x ≋ x') 
  (h-f : ∀ v -> ∞ ⊢ f v ≋ f' v) -> i ⊢ (bind x f) ≋ (bind x' f')
 bind-≋ {i} {x} {x'} {f} {f'} h-x h-f = 
  ptrans (bindx-≋ {f = f} h-x) (bindf-≋ {x = x'} h-f)
