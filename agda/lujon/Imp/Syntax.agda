------------------------------------------------------------------------
-- The syntax of Imp
------------------------------------------------------------------------
module Imp.Syntax where

open import Data.Integer
open import Imp.Syntax.Bool public
open import Imp.Syntax.Arith public
open import Imp.Syntax.Ident public
open import Imp.Syntax.Command public
---


------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------

euclidean-division : Command 
euclidean-division = 
 "r" := (var "a") , 
 "q" := (const 0ℤ) , 
 while⟨ (leq (var "b") (var "r")) ⟩ (
  "r" := (minus (var "r") (var "b")) , 
  "q" := (plus (var "q") (const (+ 1)))
 )
