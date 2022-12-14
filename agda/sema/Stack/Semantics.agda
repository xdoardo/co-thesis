------------------------------------------------------------------------
-- Small step semantics for Stack
------------------------------------------------------------------------

module Stack.Semantics where 

open import Data.Maybe
open import Data.Product
open import Stack.Syntax
open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≤ᵇ_)
open import Data.List renaming (_∷_ to _::_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Data.Integer as ℤ using (0ℤ ; +_ ; _≤ᵇ_) 
   renaming (_+_ to _+z_ ; _-_ to _-z_ ; _*_ to _*z_ ; _/_ to _/z_)
---


------------------------------------------------------------------------
-- The Stack semantics as a small-step relational transition system.
------------------------------------------------------------------------
data Transition (c : Code) : Config -> Config -> Set where
 =>const : ∀ pc σ s n -> instr-at c pc ≡ just (iconst n) ->
            Transition c ( pc , σ , s ) (pc + 1 , n :: σ , s)
 =>var : ∀ pc σ s id v -> instr-at c pc ≡ just (ivar id) -> 
          (s id) ≡ just v -> Transition c (pc , σ , s) (pc + 1 , v :: σ , s)
 =>setvar : ∀ pc σ s id n -> instr-at c pc ≡ just (isetvar id) -> 
           Transition c (pc , n :: σ , s) (pc + 1 , σ , update id n s)
 =>mul : ∀ pc σ s n₁ n₂ -> instr-at c pc ≡ just imul -> 
           Transition c (pc , n₂ :: n₁ :: σ , s) (pc + 1 , (n₁ *z n₂) :: σ , s)
 =>div : ∀ pc σ s n₁ n₂ -> (nz : ℤ.NonZero n₂) -> instr-at c pc ≡ just imul -> 
           Transition c (pc , n₂ :: n₁ :: σ , s) (pc + 1 , (_/z_ n₁ n₂ {{nz}}) :: σ , s)
 =>add : ∀ pc σ s n₁ n₂ -> instr-at c pc ≡ just iadd -> 
           Transition c (pc , n₂ :: n₁ :: σ , s) (pc + 1 , (n₁ +z n₂) :: σ , s)
 =>opp : ∀ pc σ s n -> instr-at c pc ≡ just iopp -> 
           Transition c (pc , n :: σ , s) (pc + 1 , (0ℤ -z n) :: σ , s)
 =>branch : ∀ pc σ s d pc₁ -> instr-at c pc ≡ just (ibranch d) ->  
             + pc₁ ≡ (+ pc) +z (+ 1) +z d -> Transition c ( pc , σ , s ) (pc₁ , σ , s)
 =>beq : ∀ pc σ s d₁ d₀ n₁ n₂ pc₁ -> instr-at c pc ≡ just (ibeq d₁ d₀) -> 
           + pc₁ ≡ (+ pc) +z (+ 1) +z (if ((n₁ ≤ᵇ n₂) ∧ (n₂ ≤ᵇ n₁)) then d₁ else d₀) -> 
            Transition c (pc , n₂ :: n₁ :: σ , s) (pc₁ , σ , s)
 =>bleq : ∀ pc σ s d₁ d₀ n₁ n₂ pc₁ -> instr-at c pc ≡ just (ibleq d₁ d₀) -> 
           + pc₁ ≡ (+ pc) +z (+ 1) +z (if (n₁ ≤ᵇ n₂) then d₁ else d₀) -> 
            Transition c (pc , n₂ :: n₁ :: σ , s) (pc₁ , σ , s)

-- Sequences of machine transitions define the behavior of a code.
Transitions : ∀ (c : Code) -> Config -> Config -> Set 
Transitions c = Star (Transition c)
