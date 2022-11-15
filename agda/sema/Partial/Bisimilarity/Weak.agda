------------------------------------------------------------------------
-- Weak bisimilarity for the partiality monad 
------------------------------------------------------------------------

module Partial.Bisimilarity.Weak where 

open import Size
open import Level
open import Data.Maybe using (Maybe)
open import Codata.Sized.Delay using (Delay)
open import Codata.Sized.Thunk
open import Relation.Binary
---

open Delay
open Thunk
open Maybe 
---

data bisim {a} {A : Set a} (i : Size) : (a? b? : Delay (Maybe A) ∞) -> Set where
  ~now : ∀ {a} -> bisim i (now a) (now a)
  ~later : ∀ {xs ys} (eq : Thunk^R (bisim) i xs ys) -> bisim i (later xs) (later ys)
  ~laterₗ : ∀ {xs ys} ->  bisim i (force xs) ys -> bisim i (later xs) ys
  ~laterᵣ : ∀ {xs ys} ->  bisim i xs (force ys) -> bisim i xs (later ys)

_~_ = λ {i a} {A : Set a} xa xb -> bisim {a} {A} i xa xb

-- Bisimilarity is reflexive
mutual 

  reflexive : ∀ {a A i} -> Reflexive (bisim {a} {A} i) 
  reflexive {a} {A} {i} {now x} = ~now
  reflexive {a} {A} {i} {later x} = ~later (λ where .force -> reflexive)

-- Reflexivity Examples
module _ where
open import Partial.Base

_ : ∀ {i a A} -> bisim {a} {A} i fail fail
_ = reflexive

_ : ∀ {i a A} -> bisim {a} {A} i never never 
_ = reflexive

-- Weak bisim. examples
module _ where 
  open import Data.Nat
  open import Agda.Builtin.Equality using (_≡_)
  postpone : ∀ {i a A} -> (x : Delay {a} (Maybe A) i) -> Thunk (Delay {a} (Maybe A)) i
  force (postpone x) = x
  
  _ : ∀ {ℓ} {A : Set ℓ} {a} -> (later (postpone {∞} {ℓ} {A} a)) ~ a
  _ = ~laterₗ (reflexive)
