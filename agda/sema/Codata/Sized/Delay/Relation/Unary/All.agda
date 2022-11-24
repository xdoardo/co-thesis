------------------------------------------------------------------------
-- An All predicate for the Delay monad
------------------------------------------------------------------------

module Codata.Sized.Delay.Relation.Unary.All where

open import Size
open import Effect.Monad
open import Agda.Primitive
open import Codata.Sized.Delay 
open import Codata.Sized.Thunk
open import Codata.Sized.Delay.Effectful 
-- 

open Sequential renaming (monad to delayMonad)
module _ {ℓ}  where 
  open RawMonad {ℓ} delayMonad
  --
  
  -- All P x means that if x terminates with the value v, then P v
  -- holds.
  data All {p} {A : Set ℓ} (P : A -> Set p) i : Delay A ∞ -> Set (ℓ ⊔ p) where
    now   : ∀ {v} (p : P v)                 -> All P i (now v)
    later : ∀ {x} (p : Thunk^P (All P) i x) -> All P i (later x)
  
  -- Bind respects P. 
  _>>=-cong_ : ∀ {p q i} {A B : Set ℓ} {P : A → Set p} {Q : B → Set q} {x : Delay A ∞}
                {f : A → Delay B ∞} -> All P i x -> (∀ {x} → P x → All Q i (f x)) ->
                 All Q i (x >>= f)
  now p   >>=-cong f = f p
  later p >>=-cong f = later (λ where .force -> (force p) >>=-cong f) 
