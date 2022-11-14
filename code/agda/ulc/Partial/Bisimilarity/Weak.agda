------------------------------------------------------------------------
-- Weak bisimilarity for the partiality monad 
------------------------------------------------------------------------

module Partial.Bisimilarity.Weak where 

open import Agda.Builtin.Size
open import Data.Maybe using (Maybe)
open import Codata.Sized.Delay using (Delay)
open import Codata.Sized.Thunk using (Thunk)
open import Effect.Monad
--- 

open Delay
open Thunk
open Maybe
--- 

mutual

  data _≈_ {i : Size} {A : Set} : (a? b? : Delay (Maybe A) ∞) → Set where
    ≈now : ∀ a -> now a ≈ now a
    ≈later : ∀ {a b} -> force a ≈<∞ i >≈ force b -> later a ≈ later b
    ≈laterₗ : ∀ {a b} -> force a ≈ b -> later a ≈ b
    ≈laterᵣ : ∀ {a b} -> a ≈ force b -> a ≈ later b

  _≈<_>≈_ = λ {A} a? i b? -> _≈_ {i} {A} a? b?

  record _≈<∞_>≈_ {A} (a : Delay (Maybe A) ∞) i (b : Delay (Maybe A) ∞) : Set where
    coinductive
    field 
     ≈force : {j : Size< i} → a ≈< j >≈ b

  _∞≈_ = λ {i} {A} a∞ b∞ -> _≈<∞_>≈_ {A} a∞ i b∞
open _≈<∞_>≈_

mutual 
  ≈-refl : ∀ {i : Size} {A} {a : Delay (Maybe A) ∞} -> a ≈< i >≈ a
  ≈-refl {i} {_} {now x} = ≈now x
  ≈-refl {i} {_} {later x} = ≈later (≈∞-refl {i} {_} {force x})

  ≈∞-refl : ∀ {i : Size} {A} {a : Delay (Maybe A) ∞} -> a ≈<∞ i >≈ a
  ≈force (≈∞-refl {i} {_} {a}) {j} = ≈-refl {j} {_} {a}


module _ where
  open import Partial.Base

  _ : ∀ {A : Set} -> fail {∞} {A} ≈ fail {∞} {A}
  _ = ≈-refl

  _ : ∀ {A : Set} -> force (never {∞} {A}) ≈ force (never {∞} {A})
  _ = ≈-refl
  
  _ : ∀ {A : Set} -> later (delay (fail {∞} {A})) ≈ fail {∞} {A}
  _ = ≈laterₗ (≈-refl)

  _ : ∀ {A : Set} -> fail {∞} {A} ≈ later (delay (fail {∞} {A}))
  _ = ≈laterᵣ (≈-refl)
