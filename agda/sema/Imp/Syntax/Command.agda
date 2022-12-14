------------------------------------------------------------------------
-- Command terms of IMP
------------------------------------------------------------------------
module Imp.Syntax.Command where 

open import Imp.Syntax.Bool
open import Imp.Syntax.Arith
open import Imp.Syntax.Ident
---

data Command : Set where 
 skip : Command 
 assign : (id : Ident) -> (a : AExp) -> Command 
 seq : (c₁ : Command) -> (c₂ : Command) -> Command
 ifelse : (b : BExp) -> (c₁ : Command) -> (c₂ : Command) -> Command
 while : (b : BExp) -> (c : Command) -> Command



------------------------------------------------------------------------
-- Useful shortands for commands
------------------------------------------------------------------------
infixr 5 _,_ 
infix 10 _:=_ 
infix 15 if_then_else_ while⟨_⟩_

_:=_ : (id : Ident) -> (a : AExp) -> Command 
id := a = assign id a 

_,_ : (c₁ : Command) -> (c₂ : Command) -> Command
c₁ , c₂ = seq c₁ c₂ 

if_then_else_ : (b : BExp) -> (c₁ : Command) -> (c₂ : Command) -> Command
if b then c₁ else c₂ = ifelse b c₁ c₂

while⟨_⟩_ : (b : BExp) -> (c : Command) -> Command
while⟨ b ⟩ c = while b c 
