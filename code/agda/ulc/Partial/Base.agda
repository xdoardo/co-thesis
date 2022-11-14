------------------------------------------------------------------------
-- Basic definitions for the partiality monad
------------------------------------------------------------------------

module Partial.Base where 
open import Codata.Sized.Delay using (Delay)
open import Data.Maybe using (Maybe)
open import Codata.Sized.Thunk using (Thunk)
---

open Delay
open Thunk
open Maybe
---

-- A failing computation
fail : ∀ {i} {A : Set} -> Delay (Maybe A) i
fail = now nothing

-- A never terminating computation
never : ∀ {i} {A : Set} -> Thunk (Delay (Maybe A)) i
force (never {i}) {j} = later (never {j})

-- Delay a computation.
delay : ∀ {i} {A : Set} -> (Delay (Maybe A) i) -> Thunk (Delay (Maybe A)) i
force (delay a) = a
