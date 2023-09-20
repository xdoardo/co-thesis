------------------------------------------------------------------------
-- The characteristic function datatype 
------------------------------------------------------------------------
open import Data.Bool
open import Data.Bool.Properties
---

module Data.CharacteristicFunction {a} (A : Set a) (_==_ : A -> A -> Bool) where

open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality

CharacteristicFunction : Set a
CharacteristicFunction = A -> Bool 

∅ : CharacteristicFunction
∅ = λ _ -> false

_↦_ : (v : A) -> (s : CharacteristicFunction) -> CharacteristicFunction
(v ↦  s) x = (v == x) ∨ (s x) 

_⊝_ : (v : A) -> (s : CharacteristicFunction) -> CharacteristicFunction
(v ⊝ s) x = not (v == x) ∧ (s x)

_∪_ : (s₁ s₂ : CharacteristicFunction) -> CharacteristicFunction
(s₁ ∪ s₂) x = (s₁ x) ∨ (s₂ x)

_∩_ : (s₁ s₂ : CharacteristicFunction) -> CharacteristicFunction
(s₁ ∩ s₂) x = (s₁ x) ∧ (s₂ x)

_⊏_ : (s₁ s₂ : CharacteristicFunction) -> CharacteristicFunction
(s₁ ⊏ s₂) x =  (s₁ x) ∧ not (s₂ x)

_⊆_ : (s₁ s₂ : CharacteristicFunction) -> Set a
s₁ ⊆ s₂ = ∀ x -> (x-in-s₁ : s₁ x ≡ true) -> s₂ x ≡ true

------------------------------------------------------------------------
-- Properties of the indicator function datatype 
------------------------------------------------------------------------
module Properties where 

 private
  postulate
   -- We must postulate extensionality.
   ext : ∀ a b -> Extensionality a b

  -- Extensional equality for VarsSet.
 if-ext : ∀ {s₁ s₂ : CharacteristicFunction} -> (a-ex : ∀ x -> s₁ x ≡ s₂ x) -> s₁ ≡ s₂
 if-ext a-ex = ext a Agda.Primitive.lzero a-ex
 

 private
  ∪-∅-ext : ∀ {s : CharacteristicFunction} x -> (s ∪ ∅) x ≡ s x
  ∪-∅-ext {s} x with (s x) 
  ... | false = refl
  ... | true = refl

 ∪-∅ : ∀ {s : CharacteristicFunction} -> (s ∪ ∅) ≡ s
 ∪-∅ {s} = if-ext ∪-∅-ext

 ↦=>⊆ : ∀ {id} {s : CharacteristicFunction} -> s ⊆ (id ↦ s)
 ↦=>⊆ {id} {s} id₁ id-in-s  with (id == id₁) 
 ... | false = id-in-s
 ... | true = refl

 ⊆=>∩ : ∀ {s s₁ s₂ : CharacteristicFunction} (h-1 : s ⊆ s₁) (h-2 : s ⊆ s₂) -> s ⊆ (s₁ ∩ s₂)
 ⊆=>∩ h-1 h-2 x x-in-s₁ rewrite (h-1 x x-in-s₁) rewrite (h-2 x x-in-s₁) = refl 

 ∪=>⊆ : ∀ {s s' : CharacteristicFunction} -> s ⊆ (s ∪ s')
 ∪=>⊆ {s} {s'} x x-in-s₁ rewrite x-in-s₁ = refl 

 ∪-⊆=>⊆ : ∀ {s s' s''} (h-⊆ : (s ∪ s') ⊆ s'') -> s ⊆ s''
 ∪-⊆=>⊆ {s} {s'} {s''} h-⊆ x x-in-s₁  with (h-⊆ x)
 ... | n with (s' x) 
 ... | false rewrite x-in-s₁ rewrite (∨-zeroʳ false) = n refl
 ... | true rewrite x-in-s₁ = n refl

 ⊆-∪=>⊆ : ∀ {s s' s''} (h-⊆ : s ⊆ s') -> (s ∪ s'') ⊆ (s' ∪ s'')
 ⊆-∪=>⊆ {s} {s'} {s''} h-⊆ x x-in-s₁ with (s x) in eq-sx
 ... | false with (s'' x) 
 ... | true = ∨-zeroʳ (s' x)
 ⊆-∪=>⊆ {s} {s'} {s''} h-⊆ x x-in-s₁ | true rewrite (h-⊆ x eq-sx) = refl 

 in-⊆ : ∀ {s s' s''} {i} -> (h : s i ≡ true) (h≡ : s'' ≡ (s ∪ s')) -> s'' i ≡ true
 in-⊆ {s} {s'} {s''} {i} h h≡ rewrite h≡ = (∪=>⊆ {s} {s'}) i h

 ⊆-trans : ∀ {s₁ s₂ s₃ : CharacteristicFunction} -> (s₁⊆s₂ : s₁ ⊆ s₂) -> (s₂⊆s₃ : s₂ ⊆ s₃) -> s₁ ⊆ s₃
 ⊆-trans {s₁} {s₂} {s₃} s₁⊆s₂ s₂⊆s₃ x x∈s₁ with (s₂ x)
 ... | false = s₂⊆s₃ x (s₁⊆s₂ x x∈s₁)
 ... | true = s₂⊆s₃ x (s₁⊆s₂ x x∈s₁)
