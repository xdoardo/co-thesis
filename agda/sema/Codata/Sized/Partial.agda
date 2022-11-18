------------------------------------------------------------------------
-- The partiality type and some operations
------------------------------------------------------------------------

module Codata.Sized.Partial where 

open import Size
open import Data.Nat
open import Codata.Sized.Conat
open import Data.Maybe using (Maybe)
open import Codata.Sized.Delay using (Delay) renaming (map to delayMap)
open import Codata.Sized.Thunk using (Thunk)
---

open Delay
open Thunk
open Maybe 
---

module _ {a} {A : Set a}where

 length : ∀ {i} -> Delay (Maybe A) i -> Conat i
 length (now _)   = zero
 length (later d) = suc λ where .force -> length (d .force)

 runFor : ℕ -> Delay (Maybe A) ∞ -> Maybe A
 runFor zero (now x) = x 
 runFor zero (later x) = nothing 
 runFor (suc n) (now x) = x 
 runFor (suc n) (later x) = runFor n (force x)

 fail : ∀ {i} -> Delay {a} (Maybe A) i
 fail = now nothing
 
 never : ∀ {i} -> Delay (Maybe A) i
 never = later λ where .force -> never

module _ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} where

 map : (A -> B) -> ∀ {i} -> Delay (Maybe A) i -> Delay (Maybe B) i
 map f (now (just x)) = now (just (f x))
 map f (now nothing) = now nothing 
 map f (later x) = later (λ where .force -> map f (x .force))  

 bind : ∀ {i} -> Delay {ℓ} (Maybe A) i -> (A -> Delay {ℓ′}(Maybe B) i) -> Delay {ℓ′} (Maybe B) i
 bind (now (just x)) f = f x
 bind (now nothing) f = now nothing 
 bind (later x) f = later (λ where .force -> bind (x .force) f) 
