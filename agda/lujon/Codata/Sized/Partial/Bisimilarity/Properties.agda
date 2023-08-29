------------------------------------------------------------------------
-- Weak bisimilarity for the partiality monad 
------------------------------------------------------------------------

module Codata.Sized.Partial.Bisimilarity.Properties where 

open import Size
open import Data.Empty
open import Data.Maybe
open import Codata.Sized.Delay
open import Relation.Binary.PropositionalEquality
open import Codata.Sized.Partial.Bisimilarity.Core
--- 

-- @TODO
postulate
 never≈now=>⊥ : ∀ {a} {A : Set a} {j} {i} (x : Delay (Maybe A) ∞)  -> (x⇑ : i ⊢ x ≈ never) -> (eq-now : x ≡ now j) -> ⊥
