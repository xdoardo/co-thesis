------------------------------------------------------------------------
-- An All predicate for the Partiality monad
------------------------------------------------------------------------

module Codata.Sized.Partial.Relation.Unary.All where

open import Size
open import Effect.Monad
open import Agda.Primitive
open import Codata.Sized.Thunk
open import Codata.Sized.Partial 
open import Data.Maybe hiding (_>>=_)
open import Codata.Sized.Delay hiding (bind)
open import Relation.Binary.PropositionalEquality
open import Codata.Sized.Partial.Effectful renaming (monad to partialityMonad)
-- 

-- All P x means that if x terminates with the value v, then P v
-- holds.
data All {ℓ p} {A : Set ℓ} (P : A -> Set p) i : Delay (Maybe A) ∞ -> Set (ℓ ⊔ p) where
  now   : ∀ {v} (p : P v)                 -> All P i (now (just v))
  later : ∀ {x} (p : Thunk^P (All P) i x) -> All P i (later x)

-- Bind preserves All in the following way:
_>>=-cong_ : ∀ {ℓ p q} {i} {A B : Set ℓ} {P : A -> Set p} {Q : B -> Set q} 
              {x : Delay (Maybe A) ∞} {f : A -> Delay (Maybe B) ∞} -> 
               All P i x -> (∀ {x} -> P x -> All Q i (f x)) -> All Q i (bind x f)
now p >>=-cong f = f p
later p >>=-cong f = later λ where .force -> (force p) >>=-cong f

module Reasoning {a p}
                 {A : Set a} {P : A -> Set p} where

  infixr 2 _≡<_>_ _≡<_>

  _≡<_>_ : ∀ x {y} {i} -> x ≡ y -> All P i y -> All P i x
  _ ≡< _≡_.refl > p = p 

  _≡<_> : ∀  x {i} -> All P i x -> All P i x
  _ ≡< p > = p
