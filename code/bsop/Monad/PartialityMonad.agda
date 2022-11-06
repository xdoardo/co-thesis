---------------------------------------------------------------------------
-- The Partiality monad
---------------------------------------------------------------------------
module Monad.PartialityMonad where

open import Category.Monad
open import Function 
open import Lambda.Syntax
open import Agda.Builtin.Size
open import Monad.DelayMonad using (Delay) renaming (_>>=_ to _D>>=_)
open import Monad.SizedMaybeMonad using (Maybe) renaming (_>>=_ to _M>>=_)


-- How to make this sized?
--maybe : {A : Set} {B : Maybe A → Set} →
--        ((x : A) → B (just x)) → B nothing → (x : Maybe A) → B x
--maybe j n (just x) = j x
--maybe j n nothing  = n

PartialityMonad : ∀ {i : Size} -> RawMonad (Delay i ∘ (Maybe i))
PartialityMonad {i} = record 
  {
    return = Delay.now ∘ Maybe.just 
    ; _>>=_ = λ m f -> m D>>= λ v -> ?
  }
