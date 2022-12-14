------------------------------------------------------------------------
-- Arithmetic terms of IMP
------------------------------------------------------------------------
module Imp.Syntax.Term.Arith where 

open import Data.Or
open import Data.Maybe
open import Imp.Syntax.Term.Ident
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality
--- 

Store : Set
Store = Ident -> Maybe ℤ 

data AExp : Set where 
 const : ℤ -> AExp
 var   : Ident -> AExp 
 plus  : (a₁ : AExp) -> (a₂ : AExp) -> AExp
 minus : (a₁ : AExp) -> (a₂ : AExp) -> AExp
 times : (a₁ : AExp) -> (a₂ : AExp) -> AExp
 div   : (a₁ : AExp) -> (a₂ : AExp) -> AExp


------------------------------------------------------------------------
-- Properties and lemmas of arithmetic expressions
------------------------------------------------------------------------

data _∈_ (x : Ident) : AExp -> Set where 
 ∈-var  : x ∈ var x
 ∈-plus : ∀ a₁ a₂ -> Or (x ∈ a₁) (x ∈ a₂) -> x ∈ (plus a₁ a₂)
 ∈-minus : ∀ a₁ a₂ -> Or (x ∈ a₁) (x ∈ a₂) -> x ∈ (minus a₁ a₂)
 ∈-times : ∀ a₁ a₂ -> Or (x ∈ a₁) (x ∈ a₂) -> x ∈ (times a₁ a₂)
 ∈-div : ∀ a₁ a₂ -> Or (x ∈ a₁) (x ∈ a₂) -> x ∈ (div a₁ a₂)

-- Two stores are applicatively equal iff. when an identifier appears in an
-- expression the stores hold the same value for the identifier
data _≈_⟨_⟩  (s₁ : Store) (s₂ : Store) : AExp -> Set where 
 ≈-var : ∀ (i : Ident) -> (sameId : s₁ i ≡ s₂ i) -> s₁ ≈ s₂ ⟨ var i ⟩
 ≈-plus : ∀ a₁ a₂ -> s₁ ≈ s₂ ⟨ a₁ ⟩ ->  s₁ ≈ s₂ ⟨ a₂ ⟩ ->  s₁ ≈ s₂ ⟨ plus a₁ a₂ ⟩
 ≈-minus : ∀ a₁ a₂ -> s₁ ≈ s₂ ⟨ a₁ ⟩ ->  s₁ ≈ s₂ ⟨ a₂ ⟩ ->  s₁ ≈ s₂ ⟨ minus a₁ a₂ ⟩
 ≈-times : ∀ a₁ a₂ -> s₁ ≈ s₂ ⟨ a₁ ⟩ ->  s₁ ≈ s₂ ⟨ a₂ ⟩ ->  s₁ ≈ s₂ ⟨ times a₁ a₂ ⟩
 ≈-div : ∀ a₁ a₂ -> s₁ ≈ s₂ ⟨ a₁ ⟩ ->  s₁ ≈ s₂ ⟨ a₂ ⟩ ->  s₁ ≈ s₂ ⟨ div a₁ a₂ ⟩
