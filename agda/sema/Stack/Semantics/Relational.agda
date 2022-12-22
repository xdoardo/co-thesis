------------------------------------------------------------------------
-- Relational semantics for Stack
------------------------------------------------------------------------

module Stack.Semantics.Relational where 

open import Data.Maybe
open import Data.Product
open import Stack.Syntax
open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≤ᵇ_)
open import Stack.Syntax.Properties
open import Data.List renaming (_∷_ to _::_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Data.Integer as ℤ using (0ℤ ; +_ ; _≤ᵇ_) 
   renaming (_+_ to _+z_ ; _-_ to _-z_ ; _*_ to _*z_ ; _/_ to _/z_)
---


------------------------------------------------------------------------
-- The Stack semantics as a small-step relational transition system.
------------------------------------------------------------------------
data Transition : State -> State -> Set where
 =>const : ∀ c pc σ s n -> instr-at c pc ≡ just (iconst n) ->
            Transition (c , pc , σ , s ) (c , pc + 1 , n :: σ , s)
 =>var : ∀ c pc σ s id v -> instr-at c pc ≡ just (ivar id) -> 
          (s id) ≡ v -> Transition (c , pc , σ , s) (c , pc + 1 , v :: σ , s)
 =>setvar : ∀ c pc σ s id n -> instr-at c pc ≡ just (isetvar id) -> 
           Transition (c , pc , n :: σ , s) (c , pc + 1 , σ , update id n s)
 =>mul : ∀ c pc σ s n₁ n₂ -> instr-at c pc ≡ just imul -> 
           Transition (c , pc , n₂ :: n₁ :: σ , s) (c , pc + 1 , (n₁ *z n₂) :: σ , s)
 =>div : ∀ c pc σ s n₁ n₂ -> (nz : ℤ.NonZero n₂) -> instr-at c pc ≡ just imul -> 
           Transition (c , pc , n₂ :: n₁ :: σ , s) (c , pc + 1 , (_/z_ n₁ n₂ {{nz}}) :: σ , s)
 =>add : ∀ c pc σ s n₁ n₂ -> instr-at c pc ≡ just iadd -> 
           Transition (c , pc , n₂ :: n₁ :: σ , s) (c , pc + 1 , (n₁ +z n₂) :: σ , s)
 =>opp : ∀ c pc σ s n -> instr-at c pc ≡ just iopp -> 
           Transition (c , pc , n :: σ , s) (c , pc + 1 , (0ℤ -z n) :: σ , s)
 =>branch : ∀ c pc σ s d pc₁ -> instr-at c pc ≡ just (ibranch d) ->  
             + pc₁ ≡ (+ pc) +z (+ 1) +z d -> Transition ( c , pc , σ , s ) (c , pc₁ , σ , s)
 =>beq : ∀ c pc σ s d₁ d₀ n₁ n₂ pc₁ -> instr-at c pc ≡ just (ibeq d₁ d₀) -> 
           + pc₁ ≡ (+ pc) +z (+ 1) +z (if ((n₁ ≤ᵇ n₂) ∧ (n₂ ≤ᵇ n₁)) then d₁ else d₀) -> 
            Transition (c , pc , n₂ :: n₁ :: σ , s) (c , pc₁ , σ , s)
 =>bleq : ∀ c pc σ s d₁ d₀ n₁ n₂ pc₁ -> instr-at c pc ≡ just (ibleq d₁ d₀) -> 
           + pc₁ ≡ (+ pc) +z (+ 1) +z (if (n₁ ≤ᵇ n₂) then d₁ else d₀) -> 
            Transition (c , pc , n₂ :: n₁ :: σ , s) (c , pc₁ , σ , s)

-- Sequences of machine transitions define the behavior of a code.
Transitions : State -> State -> Set 
Transitions = Star (Transition)

_=>_ : (s₁ : State) -> (s₂ : State) -> Set 
s₁ => s₂ = Transitions s₁ s₂ 
