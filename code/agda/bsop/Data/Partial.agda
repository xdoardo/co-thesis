---------------------------------------------------------------------------
-- The Partiality monad
---------------------------------------------------------------------------
module Data.Partial where

open import Agda.Builtin.Size
open import Category.Monad
open import Function 
open import Lambda.Syntax
open import Data.Delay using (Delay ; ∞Delay) 
open import Data.Maybe using (Maybe)
---
open Delay 
open ∞Delay
open Maybe
---

partial : ∀ {i : Size} {A : Set} {B : Set} -> Maybe A -> (A -> Delay {i} (Maybe B)) -> Delay {i} (Maybe B)
partial nothing f = now nothing
partial (just x) f = f x

module Bind where 
mutual
  _>>=_ : ∀ {i A B} -> Delay {i} (Maybe A) -> (A -> Delay {i} (Maybe B)) -> Delay {i} (Maybe B)
  now nothing >>= f = now nothing
  now (just x) >>= f = f x  
  later x >>= f =  later (x ∞>>= f)

  _∞>>=_ : ∀ {i A B} -> ∞Delay {i} (Maybe A) -> (A -> Delay {i} (Maybe B)) -> ∞Delay {i} (Maybe B)
  force (a ∞>>= f) = (force a) >>= f

PartialityMonad : ∀ {i : Size} -> RawMonad (Delay {i} ∘ Maybe )
PartialityMonad {i} = record 
  {
    return = now ∘ just
    ; _>>=_ = _>>=_ {i}
  } where open Bind
