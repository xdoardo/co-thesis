------------------------------------------------------------------------
-- Properties of Stack compilation of Imp
------------------------------------------------------------------------
module Stack.Imp.Compile.Properties where 

open import Data.Maybe
open import Data.Product
open import Data.Integer
open import Stack.Syntax
open import Imp.Semantics 
open import Stack.Semantics
open import Stack.Imp.Compile
open import Data.Nat renaming (_+_ to _+n_)
open import Data.List renaming (_∷_ to _::_)
open import Relation.Binary.PropositionalEquality
---

data code-at : Code -> ℤ -> Code -> Set where
  at : ∀ c₁ c₂ c₃ pc -> pc ≡ (+ codelen c₁) -> code-at (c₁ ++ c₂ ++ c₃) pc c₂


-- @TODO
compile-aexp-correct : ∀ c s a pc σ v -> 
   code-at c (+ pc) (comp-aexp a) -> aeval a s ≡ just v -> 
    Transitions c (pc , σ , s) (pc +n codelen (comp-aexp a) , v :: σ , s)
compile-aexp-correct c s a pc σ v x x₁ = ? 

