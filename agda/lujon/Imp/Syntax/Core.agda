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

------------------------------------------------------------------------
-- Properties of terms of Imp 
------------------------------------------------------------------------
module _ where 

-- Subterm relation on arithmetic expressions
data _⊑ᵃ_ : AExp -> AExp -> Set where 
 self : (a : AExp) -> a ⊑ᵃ a 
 plus-l : (a a₁ : AExp) -> a ⊑ᵃ (plus a a₁)
 plus-r : (a a₁ : AExp) -> a₁ ⊑ᵃ (plus a a₁)

-- Subterm relation on boolean expressions for other boolean expressions
data _⊑ᵇ_  : {A : Set} -> A -> BExp -> Set where 
 self : (b : BExp) -> b ⊑ᵇ b
 not : (b : BExp) -> b ⊑ᵇ (not b)
 and-l : (b₁ b₂ : BExp) -> b₁ ⊑ᵇ (and b₁ b₂)
 and-r : (b₁ b₂ : BExp) -> b₂ ⊑ᵇ (and b₁ b₂)
 le-l : (a₁ a₂ : AExp) -> a₁ ⊑ᵇ (le a₁ a₂)
 le-r : (a₁ a₂ : AExp) -> a₂ ⊑ᵇ (le a₁ a₂)

data _⊑ᶜ_ : {A : Set} -> A -> Command -> Set where 
 self : (c : Command) -> c ⊑ᶜ c
 assign : (id : Ident) (a : AExp) -> a ⊑ᶜ (assign id a)
 seq-l : (c₁ c₂ : Command) -> c₁ ⊑ᶜ (seq c₁ c₂)
 seq-r : (c₁ c₂ : Command) -> c₂ ⊑ᶜ (seq c₁ c₂)
 ifelse-b : (b : BExp) -> (c₁ c₂ : Command) -> b ⊑ᶜ (ifelse b c₁ c₂)
 ifelse-l : (b : BExp) -> (c₁ c₂ : Command) -> c₁ ⊑ᶜ (ifelse b c₁ c₂)
 ifelse-r : (b : BExp) -> (c₁ c₂ : Command) -> c₂ ⊑ᶜ (ifelse b c₁ c₂)
 while-b : (b : BExp) -> (c : Command) -> b ⊑ᶜ (while b c)
 while-c : (b : BExp) -> (c : Command) -> b ⊑ᶜ (while b c)
