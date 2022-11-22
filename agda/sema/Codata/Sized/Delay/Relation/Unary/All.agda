------------------------------------------------------------------------
-- An All predicate for the Delay monad
------------------------------------------------------------------------

module Codata.Sized.Delay.Relation.Unary.All where

open import Size
open import Agda.Primitive
open import Codata.Sized.Delay 
open import Codata.Sized.Thunk
------------------------------------------------------------------------
-- All, along with some lemmas

-- All P x means that if x terminates with the value v, then P v
-- holds.
data All {A : Set} (P : A -> Set) i : Delay (A) ∞ -> Set where
  now : ∀ {v} -> (p : P v) -> All P i (now v)
  later : ∀ {x} -> Thunk^P (All P) i x -> All P i (later x)
