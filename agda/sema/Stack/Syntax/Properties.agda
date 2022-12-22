------------------------------------------------------------------------
-- Instructions of Stack
------------------------------------------------------------------------
module Stack.Syntax.Properties where

open import Data.Maybe
open import Data.Integer
open import Data.Product
open import Stack.Syntax.Inst
open import Stack.Syntax.Ident
open import Data.Nat using (ℕ) renaming (_+_ to _+n_ ; suc to nsuc)
open import Data.List renaming (_∷_ to _::_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.List.Properties
---

-- Compute the length of a code
codelen : Code -> ℕ 
codelen x = length x

codelen-++ : ∀ c₁ {c₂} -> codelen c₁ +n codelen c₂ ≡ codelen (c₁ ++ c₂)
codelen-++ [] = refl
codelen-++ (x :: c₁) = cong nsuc (codelen-++ c₁)

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

code-at-eq : ∀ c₁ c₂ c pc -> (c₁₂-eq : c₁ ≡ c₂) -> (c₁-at : code-at c₁ pc c) -> code-at c₂ pc c
code-at-eq .(c₁ ++ c ++ c₃) .(c₁ ++ c ++ c₃) c pc refl (at c₁ .c c₃ .pc x) = at c₁ c c₃ pc x


code-at-append : ∀ c c₁ c₂ pc -> code-at c pc (c₁ ++ c₂) -> code-at c pc c₁
code-at-append code c₁ c₂ pc (at c₃ .(c₁ ++ c₂) c₄ .pc x) = code-at-assoc {c₃} {c₁} {c₂} {c₄}
 (at c₃ c₁ (c₂ ++ c₄) pc x)
 where 
  ++-assoc' : ∀ c₁ c₂ c₃ c₄ -> (c₁ ++ c₂ ++ c₃ ++ c₄) ≡ (c₁ ++ (c₂ ++ c₃) ++ c₄)
  ++-assoc' c₁ c₂ c₃ c₄ = 
   begin 
    c₁ ++ c₂ ++ c₃ ++ c₄ 
   ≡⟨ sym (cong (c₁ ++_) (++-assoc c₂ c₃ c₄))⟩ 
    c₁ ++ (c₂ ++ c₃) ++ c₄ 
   ∎
  code-at-assoc : ∀ {c₁ c₂ c₃ c₄ pc} -> code-at (c₁ ++ c₂ ++ c₃ ++ c₄) pc c₂ -> 
   code-at (c₁ ++ (c₂ ++ c₃) ++ c₄) pc c₂
  code-at-assoc {c₁} {c₂} {c₃} {c₄} {pc} x = code-at-eq (c₁ ++ c₂ ++ c₃ ++ c₄) 
   (c₁ ++ (c₂ ++ c₃) ++ c₄) c₂ pc (++-assoc' c₁ c₂ c₃ c₄) x 

code-at-next : ∀ c c₂ c₃ pc -> code-at c pc (c₂ ++ c₃) ->
                code-at c (pc +n codelen c₂) c₃
code-at-next .(c₁ ++ (c₂ ++ c₃) ++ c₄) c₂ c₃ pc (at c₁ .(c₂ ++ c₃) c₄ .pc x) =
 let 
  pc+codelen = 
   begin 
    pc +n codelen c₂ 
   ≡⟨ cong (_+n codelen c₂) x ⟩ 
    codelen c₁ +n codelen c₂
   ≡⟨ codelen-++ c₁ ⟩
    codelen (c₁ ++ c₂) 
   ∎
 in code-at-assoc c₁ c₂ c₃ c₄ (pc +n codelen c₂) (at (c₁ ++ c₂) c₃ c₄ (pc +n codelen c₂) pc+codelen)
 where 
  ++-assoc' : ∀ c₁ c₂ c₃ c₄ -> (c₁ ++ c₂) ++ c₃ ++ c₄ ≡ c₁ ++ (c₂ ++ c₃) ++ c₄
  ++-assoc' c₁ c₂ c₃ c₄ = 
   begin 
    (c₁ ++ c₂) ++ c₃ ++ c₄ 
   ≡⟨ ++-assoc c₁ c₂ (c₃ ++ c₄) ⟩ 
    c₁ ++ c₂ ++ c₃ ++ c₄ 
   ≡⟨ sym (cong (c₁ ++_) (++-assoc c₂ c₃ c₄))⟩ 
    c₁ ++ (c₂ ++ c₃) ++ c₄ 
   ∎
  code-at-assoc : ∀ c₁ c₂ c₃ c₄ pc -> code-at ((c₁ ++ c₂) ++ c₃ ++ c₄) pc c₃ ->
    code-at (c₁ ++ (c₂ ++ c₃) ++ c₄) pc c₃
  code-at-assoc c₁ c₂ c₃ c₄ pc x = code-at-eq ((c₁ ++ c₂) ++ c₃ ++ c₄) 
   (c₁ ++ (c₂ ++ c₃) ++ c₄) c₃ pc (++-assoc' c₁ c₂ c₃ c₄) x
