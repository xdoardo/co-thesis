------------------------------------------------------------------------
-- An All predicate for the Partiality monad
------------------------------------------------------------------------

module Codata.Sized.Partial.Relation.Unary.All where

open import Size
open import Effect.Monad
open import Agda.Primitive
open import Codata.Sized.Delay
open import Codata.Sized.Thunk
open import Codata.Sized.Partial 
open import Data.Maybe hiding (_>>=_)
open import Codata.Sized.Partial.Bisimilarity.Weak
open import Codata.Sized.Partial.Effectful renaming (monad to partialityMonad)
-- 

module _ {ℓ}  where 
  open RawMonad {ℓ} partialityMonad 
  --
  
  -- All P x means that if x terminates with the value v, then P v
  -- holds.
  data All {p} {A : Set ℓ} (P : A -> Set p) i : Delay (Maybe A) ∞ -> Set (ℓ ⊔ p) where
   now   : ∀ {v} (p : P v)                 -> All P i (now (just v))
   later : ∀ {x} (p : Thunk^P (All P) i x) -> All P i (later x)
   _≈<_>P_     : ∀ x {y} (x≈y : i ⊢ x ≈ y) (p : All P i y) -> All P i x
   _<_>P       : ∀ x (p : All P i x) -> All P i x
