------------------------------------------------------------------------
-- Some operations on the partiality type
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

module _ {a} {A : Set a} where

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
