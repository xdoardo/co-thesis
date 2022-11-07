---------------------------------------------------------------------------
-- The Partiality monad
---------------------------------------------------------------------------
module Monad.PartialityMonad where

open import Agda.Builtin.Size
open import Category.Monad
open import Function 
open import Lambda.Syntax
open import Monad.DelayMonad using (Delay ; ∞Delay) 
open import Monad.SizedMaybeMonad using (Maybe) 
---

open Delay 
open ∞Delay
open Maybe
---

partial : ∀ {i : Size} {A : Set} {B : Set} -> Maybe i A -> (A -> Delay i (Maybe i B)) -> Delay i (Maybe i B)
partial nothing f = now nothing
partial (just x) f = f x

module Bind where 
mutual
  _>>=_ : ∀ {i A B} -> Delay i (Maybe i A) -> (A -> Delay i (Maybe i B)) -> Delay i (Maybe i B)
  now nothing >>= f = now nothing
  now (just x) >>= f = f x  
  later x >>= f =  later (x ∞>>= f)

  _∞>>=_ : ∀ {i A B} -> ∞Delay i (Maybe i A) -> (A -> Delay i (Maybe i B)) -> ∞Delay i (Maybe i B)
  force (a ∞>>= f) = (force a) >>= f

PartialityMonad : ∀ {i : Size} -> RawMonad (Delay i ∘ (Maybe i))
PartialityMonad {i} = record 
  {
    return = now ∘ just
    ; _>>=_ = _>>=_ {i}
  } where open Bind
