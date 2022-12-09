------------------------------------------------------------------------
-- Unary convergence relation for partial types 
------------------------------------------------------------------------

module Codata.Sized.Partial.Relation.Unary.Convergence where

open import Size
open import Data.Maybe
open import Codata.Sized.Thunk
open import Data.Product using (∃)
open import Codata.Sized.Delay hiding (_⇓)
open import Codata.Sized.Partial.Relation.Binary.Convergence 

_⇓ : {A : Set} (x : Delay (Maybe A) ∞) → Set
x ⇓ = ∃ λ a → x ⇓ a
