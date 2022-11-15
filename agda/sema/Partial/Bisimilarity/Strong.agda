------------------------------------------------------------------------
-- Strong bisimilarity for the partiality monad 
------------------------------------------------------------------------

module Partial.Bisimilarity.Strong where 

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

_~_ = λ {i a} {A : Set a} xa xb -> bisim {a} {A} i xa xb

-- Bisimilarity is reflexive
mutual 

  reflexive : ∀ {a A i} -> Reflexive (bisim {a} {A} i) 
  reflexive {a} {A} {i} {now x} = ~now
  reflexive {a} {A} {i} {later x} = ~later (λ where .force -> reflexive)

-- Reflexivity Examples
module _ where
open import Partial.Base

-- @TODO (ecmm) : learn why indexing by `i` induces an error
_ : ∀ {a A} -> (fail {∞} {a} {A}) ~ (fail {∞} {a} {A})
_ = reflexive

_ : ∀ {a A} -> (never {∞} {a} {A}) ~ (never {∞} {a} {A})
_ = reflexive
