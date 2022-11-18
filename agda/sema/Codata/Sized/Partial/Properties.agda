------------------------------------------------------------------------
-- Properties of the Partiality type
------------------------------------------------------------------------

module Codata.Sized.Partial.Properties where

open import Size
open import Data.Product using (∃)
open import Data.Maybe using (Maybe)
open import Codata.Sized.Delay using (Delay) renaming (map to delayMap)
open import Codata.Sized.Thunk using (Thunk)
---

open Delay
open Thunk
open Maybe 
---

--- Convergence
module Convergence where
  open import Effect.Functor
  open RawFunctor  
  open import Codata.Sized.Partial

  data _⇓_ {a} {A : Set a} : (a? : Delay (Maybe A) ∞) (v : A) -> Set where 
    ⇓now : ∀ {v} -> (now (just v)) ⇓ v
    ⇓later : ∀ {v p} -> (force p) ⇓ v -> later p ⇓ v
  
  _⇓ : {A : Set} (x : Delay (Maybe A) ∞) → Set
  x ⇓ = ∃ λ a -> x ⇓ a

  map⇓ : ∀ {a b} {A : Set a} {B : Set b} {a? : Delay (Maybe A) ∞} {v : A} 
          (f : A -> B) -> a? ⇓ v -> (map f a?) ⇓ f v
  map⇓ f ⇓now = ⇓now 
  map⇓ f (⇓later x) = ?
