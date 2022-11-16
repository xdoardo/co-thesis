------------------------------------------------------------------------
-- Bind for the partiality (Delay ∘ Maybe) monad
------------------------------------------------------------------------

module Partial.Bind where 

open import Data.Maybe using (Maybe)
open import Codata.Sized.Delay using (Delay)
open import Codata.Sized.Thunk using (Thunk)
open import Codata.Sized.Delay renaming (map to delayMap) 
---

open Delay
open Thunk
open Maybe 
---

infixl 11 _>>=_
_>>=_ : ∀ {i a b} {A : Set a} {B : Set b} -> Delay {a} (Maybe A) i -> 
         (A -> Delay {b} (Maybe B) i) -> Delay {b} (Maybe B) i
now nothing >>= f = now nothing
now (just x) >>= f = f x  
later d >>= f =  later λ where .force -> (d .force) >>= f
