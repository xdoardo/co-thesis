------------------------------------------------------------------------
-- Identifiers and stores of Imp
------------------------------------------------------------------------
module Imp.Syntax.Ident where 

open import Data.Maybe
open import Relation.Nullary
open import Data.Bool hiding (_≟_)
open import Relation.Nullary.Decidable
open import Function.Base using (case_of_)
open import Data.Integer using (ℤ ; 0ℤ ; _≤ᵇ_ ; _≟_)
open import Data.String using (String ; _==_) renaming (_≟_ to _≟ₛ_)
---

Ident : Set 
Ident = String
 
Store : Set
Store = Ident -> Maybe ℤ 

empty : Store 
empty = λ _ -> nothing

update : (i : Ident) -> (v : ℤ) -> (s : Store) -> Store 
update i v s = λ x -> if x == i then (just v) else (s x)

join : (s₁ s₂ : Store) -> Store
join s₁ s₂ = λ id -> case (s₁ id) of λ { (just v) -> (just v) ; nothing -> (s₂ id)}

merge : (s₁ s₂ : Store) -> Store
merge s₁ s₂ = λ id -> (s₁ id) >>= λ v₁ -> (s₂ id) >>= λ v₂ -> if (⌊ v₁ ≟ v₂ ⌋) then just v₁ else nothing

------------------------------------------------------------------------
-- Properties of identifiers and stores of Imp
------------------------------------------------------------------------
module _ where
 open import Data.List
 open import Data.Maybe 
 open import Data.Product 
 open import Data.List.Membership.Propositional
 open import Relation.Binary.PropositionalEquality
 --- 

 -- identifiers equivalence 
 ≟ₛ-refl : ∀ {S : Ident} → (S ≟ₛ S) ≡ yes refl
 ≟ₛ-refl = ≡-≟-identity _≟ₛ_ refl
 
 ==-refl : ∀ {S : Ident} → (S == S) ≡ true
 ==-refl {S} = cong isYes (≟ₛ-refl {S})

-- -- Stores equivalence 
-- _≅_ : Store -> Store -> Set
-- x ≅ x₁ = ∀ {id : Ident} {z : ℤ} -> x id ≡ just z -> x₁ id ≡ just z
--
-- 
-- -- A predicate for unvalued inclusion between stores
-- _⊆ᵤ_ : ∀ (s₁ s₂ : Store) -> Set 
-- s₁ ⊆ᵤ s₂ =  ∀ id -> (∃ λ v -> s₁ id ≡ just v)  -> ∃ λ v' -> s₂ id ≡ just v'
--
-- -- Transitivity of stores  inclusion 
-- trans-⊆ᵤ : ∀ (s₁ s₂ s₃ : Store) -> (s₁⊆s₂ : s₁ ⊆ᵤ s₂) -> (s₂⊆s₃ : s₂ ⊆ᵤ s₃ ) ->  s₁ ⊆ᵤ s₃ 
-- trans-⊆ᵤ s₁ s₂ s₃ s₁⊆s₂ s₂⊆s₃ id x = s₂⊆s₃ id (s₁⊆s₂ id x)
