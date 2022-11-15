------------------------------------------------------------------------
-- Basic definitions targeting the partiality monad 
------------------------------------------------------------------------

module Partial.Base where

open import Data.Maybe using (Maybe)
open import Codata.Sized.Delay using (Delay)
open import Codata.Sized.Thunk using (Thunk)
---

open Delay
open Thunk
open Maybe 
---

-- A failing computation
fail : ∀ {i} {a} {A : Set a} -> Delay {a} (Maybe A) i
fail = now nothing


-- A non-terminating computation
never : ∀ {i a} {A : Set a} → Delay (Maybe A) i
never = later λ where .force → never
