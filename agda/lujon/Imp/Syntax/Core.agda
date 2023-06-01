------------------------------------------------------------------------
-- Core terms of the syntax of Imp 
------------------------------------------------------------------------
module Imp.Syntax.Core where 

open import Data.Integer
open import Imp.Syntax.Ident
open import Data.Bool renaming (not to notᵇ)
open import Data.List using (_∷_ ; _++_ ; List ; [] )
---


data AExp : Set where 
 const : (n : ℤ) -> AExp
 var   : (id : Ident) -> AExp 
 plus  : (a₁ a₂ : AExp) -> AExp

data BExp : Set where 
 const : (b : Bool) -> BExp
 le : (a₁ a₂ : AExp) -> BExp 
 not : (b : BExp) -> BExp 
 and : (b₁ b₂ : BExp) -> BExp 

data Command : Set where 
 skip : Command 
 assign : (id : Ident) -> (a : AExp) -> Command 
 seq : (c₁ c₂ : Command) -> Command
 ifelse : (b : BExp) -> (c₁ c₂ : Command) -> Command
 while : (b : BExp) -> (c : Command) -> Command
