------------------------------------------------------------------------
-- Instructions of Stack
------------------------------------------------------------------------
module Stack.Syntax.Properties where

open import Data.Maybe
open import Data.Integer
open import Data.Product
open import Stack.Syntax.Inst
open import Stack.Syntax.Ident
open import Data.Nat using (ℕ)
open import Data.List renaming (_∷_ to _::_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
---

-- Compute the length of a code
codelen : Code -> ℕ 
codelen x = length x

-- Get the instruction at a certain PC
instr-at : (c : Code) -> (pc : PC) -> Maybe (Inst)
instr-at [] pc = nothing
instr-at (x :: c) ℕ.zero = just x
instr-at (x :: c) (ℕ.suc pc) = instr-at c pc

-- A piece of code appears in another code at a certain PC
data code-at : Code -> PC -> Code -> Set where
  at : ∀ c₁ c₂ c₃ pc -> pc ≡ codelen c₁ -> code-at (c₁ ++ c₂ ++ c₃) pc c₂

instr-at-codelen : ∀ c₁ c c₂ -> instr-at (c₁ ++ c :: c₂ ) (codelen c₁) ≡ just (c)
instr-at-codelen [] c c₂ = refl
instr-at-codelen (x :: c₁) c c₂ = instr-at-codelen c₁ c c₂ 

code-at=>instr-at : ∀ {c₁ pc c c₂} -> code-at c₁ pc (c :: c₂) -> instr-at c₁ pc ≡ just c
code-at=>instr-at (at c₁ (c :: c₂) c₃ pc pc≡len) = 
 begin 
  instr-at (c₁ ++ c :: c₂ ++ c₃) pc 
 ≡⟨ cong (instr-at (c₁ ++ c :: c₂ ++ c₃)) pc≡len ⟩
  instr-at (c₁ ++ c :: c₂ ++ c₃) (codelen c₁)
 ≡⟨ instr-at-codelen c₁ c (c₂ ++ c₃)⟩ 
  instr-at (c :: c₂ ++ c₃) ℕ.zero 
 ≡⟨ refl ⟩ 
  just c
 ∎ 
