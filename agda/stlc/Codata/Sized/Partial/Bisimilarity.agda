------------------------------------------------------------------------
-- Weak bisimilarity for the partiality monad 
------------------------------------------------------------------------

module Codata.Sized.Partial.Bisimilarity where 

open import Size
open import Data.Maybe
open import Codata.Sized.Thunk
open import Codata.Sized.Delay  hiding (never)
open import Codata.Sized.Partial.Bisimilarity.Core public 

------------------------------------------------------------------------
-- Examples 
module _ {a b c} {A : Set a} {B : Set b} {C : Set c}
         {r} {P : A → B → Set r} {Q : B → C → Set r} {R : A → C → Set r} where

  open import Codata.Sized.Partial 

  fail-refl : ∀ {i} -> i ⊢ (fail {A = A}) ≈ (fail {A = A})
  fail-refl = refl

  never-refl : ∀ {i} -> i ⊢ (never {A = A}) ≈ (never {A = A})
  never-refl = refl

-- Weak examples 
  postpone : ∀ {i} -> (x : Delay {a} (Maybe A) i) -> Thunk (Delay {a} (Maybe A)) i
  force (postpone x) = x
  
  _ : ∀ {i x} -> i ⊢ (later (postpone x)) ≈ x
  _ = laterₗ (refl)
