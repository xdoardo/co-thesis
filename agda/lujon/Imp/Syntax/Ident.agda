{-# OPTIONS --allow-unsolved-metas #-} 
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

update : (id₁ : Ident) -> (v : ℤ) -> (s : Store) -> Store 
update id₁ v s id₂ with id₁ == id₂
... | true = (just v) 
... | false = (s id₂)

join : (s₁ s₂ : Store) -> Store
join s₁ s₂ id with (s₁ id) 
... | just v = just v
... | nothing = s₂ id

merge : (s₁ s₂ : Store) -> Store
merge s₁ s₂ = λ id -> (s₁ id) >>= λ v₁ -> (s₂ id) >>= λ v₂ -> if (⌊ v₁ ≟ v₂ ⌋) then just v₁ else nothing

remove : (i : Ident) -> (s : Store) -> Store
remove i s = λ id -> if id == i then nothing else (s id)

------------------------------------------------------------------------
-- Properties of identifiers and stores of Imp
------------------------------------------------------------------------
module _ where

 open import Data.List
 open import Data.Maybe 
 open import Data.Product 
 open import Data.List.Membership.Propositional
 open import Axiom.Extensionality.Propositional
 open import Relation.Binary.PropositionalEquality
 --- 

 private
  postulate
   -- We must postulate extensionality.
   ext : ∀ a b -> Extensionality a b

  -- Extensional equality for VarsSet.
 store-ext : ∀ {s₁ s₂ : Store} -> (a-ex : ∀ x -> s₁ x ≡ s₂ x) -> s₁ ≡ s₂
 store-ext a-ex = ext Agda.Primitive.lzero Agda.Primitive.lzero a-ex
 
 private
  update-is-join-ext : ∀ {x s id v} -> (update id v s) x ≡ (join (update id v empty) s) x
  update-is-join-ext {x} {s} {id} {v} with (id == x)
  ... | true = refl
  ... | false = refl

 update-is-join : ∀ {s id v} -> (update id v s) ≡ (join (update id v empty) s)
 update-is-join {s} {id} {v} = store-ext λ { x → update-is-join-ext {x} {s} {id} {v} } 

 -- identifiers equivalence 
 ≟ₛ-refl : ∀ {S : Ident} → (S ≟ₛ S) ≡ yes refl
 ≟ₛ-refl = ≡-≟-identity _≟ₛ_ refl
 
 ==-refl : ∀ {S : Ident} → (S == S) ≡ true
 ==-refl {S} = cong isYes (≟ₛ-refl {S})

 -- Stores equivalence 
 _≅_ : Store -> Store -> Set
 x ≅ x₁ = ∀ {id : Ident} {z : ℤ} -> x id ≡ just z -> x₁ id ≡ just z

 -- Unvalued stores inclusion
 _⊑ᵘ_ : Store -> Store -> Set
 x ⊑ᵘ x₁ = ∀ {id : Ident} -> (∃ λ z -> x id ≡ just z) -> (∃ λ z -> x₁ id ≡ just z)

 ⊑ᵘ-trans : ∀ {s₁ s₂ s₃ : Store} (h₁ : s₁ ⊑ᵘ s₂) (h₂ : s₂ ⊑ᵘ s₃) -> s₁ ⊑ᵘ s₃
 ⊑ᵘ-trans h₁ h₂ =  ? 
