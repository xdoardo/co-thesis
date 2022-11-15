------------------------------------------------------------------------
-- The sized monadic bind for the partiality monad
------------------------------------------------------------------------

module Partial.Bind where 

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
  _>>=_ : ∀ {i a b} {A : Set a} {B : Set b} -> Delay {a} (Maybe A) i -> (A -> Delay {b} (Maybe B) i) -> Delay {b} (Maybe B) i
  now nothing >>= f = now nothing
  now (just x) >>= f = f x  
  later x >>= f =  later (x ∞>>= f)

  _∞>>=_ : ∀ {i a b} {A : Set a} {B : Set b} -> Thunk (Delay {a} (Maybe A)) i -> (A -> Delay {b} (Maybe B) i) -> Thunk (Delay {b} (Maybe B)) i
  force (a ∞>>= f) = (force a) >>= f
