------------------------------------------------------------------------
-- The semantics of Scheme 
-----------------------------------------------------------------------
module Scheme.Semantics where

open import Size
open import Partial.Base
open import Partial.Bind
open import Scheme.Syntax
open import Data.Nat using (suc)
open import Data.Vec using (_∷_ ; Vec)
open import Data.Maybe using (Maybe)
open import Partial.Bisimilarity.Weak
open import Codata.Sized.Delay using (Delay)
open import Codata.Sized.Thunk using (Thunk)
--- 

open Delay
open Thunk
open Maybe 
open Vec
---


mutual 

  eval : ∀ { i } -> Exp -> Env -> Delay (Maybe Exp) i
  eval (atom (symbol x)) Λ = now (lookup x Λ)
  eval (atom (int x)) Λ = now (just (atom (int x))) 
  eval (atom (float x)) Λ = now (just (atom (float x))) 
  eval (list (x ∷ x₁)) Λ = apply x x₁ Λ

  apply : ∀ { i n } -> Exp -> Vec Exp n -> Env -> Delay (Maybe Exp) i
  apply fun [] Λ = fail
  apply fun (x ∷ args) Λ = ?
