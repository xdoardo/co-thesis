{-# OPTIONS --allow-unsolved-metas #-} 
------------------------------------------------------------------------
-- Weak bisimilarity for the partiality monad 
------------------------------------------------------------------------

module Codata.Sized.Partial.Bisimilarity.Properties where 

open import Size
open import Data.Empty
open import Data.Maybe
open import Codata.Sized.Thunk
open import Codata.Sized.Delay
open import Relation.Binary.PropositionalEquality
open import Codata.Sized.Partial.Bisimilarity.Core
open import Codata.Sized.Partial.Effectful renaming (bind to _>>=ᵖ_)
open import Codata.Sized.Partial.Bisimilarity.Relation.Binary.Equivalence using (≡=>≈)
--- 

module _ {a} {A : Set a} where
