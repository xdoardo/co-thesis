------------------------------------------------------------------------
-- Convergence relation for partial types 
------------------------------------------------------------------------

module Codata.Sized.Partial.Relation.Binary.Convergence where

open import Size
open import Data.Maybe
open import Codata.Sized.Delay
open import Codata.Sized.Thunk
---

data _⇓_ {A : Set} : (a? : Delay (Maybe A) ∞) (a : A) -> Set where
 now⇓ : ∀ {a} -> now (just a) ⇓ a
 later⇓ : ∀ {a} {a∞ : Thunk (Delay (Maybe A)) ∞} -> force a∞ ⇓ a -> later a∞ ⇓ a
