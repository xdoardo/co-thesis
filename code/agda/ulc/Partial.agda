------------------------------------------------------------------------
-- The partiality monad 
------------------------------------------------------------------------

module Partial where 


open import Agda.Builtin.Size
open import Data.Maybe using (Maybe)
open import Codata.Sized.Delay using (Delay)
open import Codata.Sized.Thunk using (Thunk)
open import Data.Nat
---

open Delay
open Thunk
open Maybe 
---

mutual
  _>>=_ : ∀ {i} {A : Set0} {B : Set0} -> Delay (Maybe A) i -> (A -> Delay (Maybe B) i) -> Delay (Maybe B) i
  now nothing >>= f = now nothing
  now (just x) >>= f = f x  
  later x >>= f =  later (x ∞>>= f)

  _∞>>=_ : ∀ {i} {A : Set0} {B : Set0} -> Thunk (Delay (Maybe A)) i -> (A -> Delay (Maybe B) i) -> Thunk (Delay (Maybe B)) i
  force (a ∞>>= f) = (force a) >>= f


-- A failing computation
fail : ∀ {A : Set0} {i} -> Delay (Maybe A) i
fail = now nothing

-- A never terminating computation
never : ∀ {A : Set0} {i} -> Thunk (Delay (Maybe A)) i
force (never {A} {j}) {i} = later (never {A} {i})


module Equality where
  -- Weak bisimilarity
  mutual 
   data _≈_ {A : Set0} {i} : Delay (Maybe A) i -> Delay (Maybe A) i -> Set where 
    ≈now    : ∀ {x : Maybe A}                                                             -> now x ≈ now x
    ≈later  : ∀ {x : Thunk (Delay (Maybe A)) ∞} {y : Thunk (Delay (Maybe A)) ∞} -> (force x) ≈ (force y) -> (later x) ≈ (later y)
    ≈laterˡ : ∀ {x : Thunk (Delay (Maybe A)) ∞} {y : Delay (Maybe A) ∞ } -> (force x) ≈ y -> (later x) ≈ y 
    ≈laterʳ : ∀ {x : Delay (Maybe A) ∞ } {y : Thunk (Delay (Maybe A)) ∞} -> x ≈ (force y) -> x ≈ (later y)

  _ : ∀ {A} -> (fail {A = A} ≈ fail {A = A})
  _ = ≈now

  -- a : ∀ {i : Size} {j : Size< i} {A : Set0} -> (force (never {A} {j}) {i} ≈ force (never {A = A}))
  -- a {i} {A} = ≈later {x = (never {i = i})}{y = never {i}} (force never ≈ force never)
