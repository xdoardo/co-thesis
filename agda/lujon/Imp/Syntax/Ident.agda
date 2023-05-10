------------------------------------------------------------------------
-- Identifiers and stores of Imp
------------------------------------------------------------------------
module Imp.Syntax.Ident where 

open import Data.Maybe
open import Relation.Nullary
open import Data.Bool hiding (_≟_)
open import Relation.Nullary.Decidable
open import Data.String using (String ; _==_ )
open import Data.Integer using (ℤ ; 0ℤ ; _≤ᵇ_ ; _≟_)
---

Ident : Set 
Ident = String
 
Store : Set
Store = Ident -> Maybe ℤ 

empty : Store 
empty = λ _ -> nothing

update : (i : Ident) -> (v : ℤ) -> (s : Store) -> Store 
update i v s = λ x -> if x == i then (just v) else (s x)

merge : (s₁ s₂ : Store) -> Store
merge s₁ s₂ = λ id -> (s₁ id) >>= λ v₁ -> (s₂ id) >>= λ v₂ -> if (⌊ v₁ ≟ v₂ ⌋) then just v₁ else nothing

------------------------------------------------------------------------
-- Properties of identifiers and stores of Imp
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality

_≅_ : Store -> Store -> Set
x ≅ x₁ = ∀ {id : Ident} {z : ℤ} -> x id ≡ just z -> x₁ id ≡ just z