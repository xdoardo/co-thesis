------------------------------------------------------------------------
-- Instructions of Stack
------------------------------------------------------------------------
module Stack.Syntax.Inst where

open import Data.List
open import Data.Maybe
open import Data.Product
open import Stack.Syntax.Ident
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
---

data Inst : Set where 
 iconst : (n : ℤ) -> Inst            -- push the integer n
 ivar : (id : Ident) -> Inst         -- push the current value of variable id
 isetvar : (id : Ident) -> Inst      -- pop an integer and assign it to variable id
 imul : Inst                         -- pop two integers, push their multiplication
 idiv : Inst                         -- pop two integers, push their division
 iadd : Inst                         -- pop two integers, push their sum
 iopp : Inst                         -- pop one integer, push its opposite
 ibranch : (d : ℤ) -> Inst           -- skip forward or backward d instructions
 ibeq : (d₁ : ℤ) -> (d₀ : ℤ) -> Inst -- pop two integers, skip d₁
                                     -- instructions if equal, d₀ if not
                                     -- equal
 ibleq : (d₁ : ℤ) (d₀ : ℤ) -> Inst   -- pop two integer, skip d₁
                                     -- instructions if less or equal, d₀ if greater
 ihalt : Inst                        -- stop execution

-- A Stack program is a list of instructions
Code : Set 
Code = List Inst

codelen : Code -> ℕ 
codelen x = length x

-- The program counter is just a natural
PC : Set
PC = ℕ

-- The actual stack is a list of integers
Stack : Set 
Stack = List ℤ

-- A configuration of the stack machine is the following triple: 
Config : Set 
Config = (PC × Stack × Store)

-- Get the instruction at a certain PC
instr-at : (c : Code) -> (pc : PC) -> Maybe (Inst)
instr-at [] pc = nothing
instr-at (x ∷ c) ℕ.zero = just x
instr-at (x ∷ c) (ℕ.suc pc) = instr-at c pc
