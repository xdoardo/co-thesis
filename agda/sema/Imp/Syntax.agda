------------------------------------------------------------------------
-- The syntax of the IMP language 
-----------------------------------------------------------------------
module Imp.Syntax where

open import Data.Integer using (ℤ)
open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)

-- (Taken from (https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html))

data AExp : Set where 
  ANum : (n : ℕ) -> AExp
  APlus : AExp -> AExp -> AExp 
  AMinus : AExp -> AExp -> AExp 
  AMult : AExp -> AExp -> AExp

data BExp : Set where
  BTrue : BExp
  BFalse : BExp
  BNot : BExp -> BExp
  BAnd : BExp -> BExp -> BExp
  BEq : AExp -> AExp -> BExp 
  BNeq : AExp -> AExp -> BExp 
  BLe : AExp -> AExp -> BExp 
  BGt : AExp -> AExp -> BExp 


