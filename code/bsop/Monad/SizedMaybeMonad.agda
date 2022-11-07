---------------------------------------------------------------------------
-- The sized Maybe monad
---------------------------------------------------------------------------

module Monad.SizedMaybeMonad where 

open import Agda.Builtin.Size 
---

data Maybe (i : Size) (A : Set) : Set where 
  nothing : Maybe i A
  just : A -> Maybe i A
