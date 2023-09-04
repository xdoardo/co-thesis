------------------------------------------------------------------------
-- The indicator function datatype 
------------------------------------------------------------------------
open import Data.Bool
---

module Data.IndicatorFunction {a} (A : Set a) (_==_ : A -> A -> Bool) where

open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality

IndicatorFunction : Set a
IndicatorFunction = A -> Bool 

∅ : IndicatorFunction
∅ = λ _ -> false

_↦_ : (v : A) -> (s : IndicatorFunction) -> IndicatorFunction
(v ↦  s) x = (v == x) ∨ (s v) 

_⊝_ : (v : A) -> (s : IndicatorFunction) -> IndicatorFunction
(v ⊝ s) x = not (v == x) ∧ (s x)

_∪_ : (s₁ s₂ : IndicatorFunction) -> IndicatorFunction
(s₁ ∪ s₂) x = (s₁ x) ∨ (s₂ x)

_∩_ : (s₁ s₂ : IndicatorFunction) -> IndicatorFunction
(s₁ ∩ s₂) x = (s₁ x) ∧ (s₂ x)

_⊏_ : (s₁ s₂ : IndicatorFunction) -> IndicatorFunction
(s₁ ⊏ s₂) x =  (s₁ x) ∧ not (s₂ x)

_⊆_ : (s₁ s₂ : IndicatorFunction) -> Set a
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
 if-ext : ∀ {s₁ s₂ : IndicatorFunction} -> (a-ex : ∀ x -> s₁ x ≡ s₂ x) -> s₁ ≡ s₂
 if-ext a-ex = ext a Agda.Primitive.lzero a-ex
 

 private
  ∪-∅-ext : ∀ {s : IndicatorFunction} x -> (s ∪ ∅) x ≡ s x
  ∪-∅-ext {s} x with (s x) 
  ... | false = refl
  ... | true = refl

 ∪-∅ : ∀ {s : IndicatorFunction} -> (s ∪ ∅) ≡ s
 ∪-∅ {s} = if-ext ∪-∅-ext

 ∪=>⊆ : ∀ {s s' : IndicatorFunction} -> s ⊆ (s ∪ s')
 ∪=>⊆ {s} {s'} x x-in-s₁ rewrite x-in-s₁ = refl 
 
 in-⊆ : ∀ {s s' s''} {i} -> (h : s i ≡ true) (h≡ : s'' ≡ (s ∪ s')) -> s'' i ≡ true
 in-⊆ {s} {s'} {s''} {i} h h≡ rewrite h≡ = (∪=>⊆ {s} {s'}) i h

 ⊆-trans : ∀ {s₁ s₂ s₃ : IndicatorFunction} -> (s₁⊆s₂ : s₁ ⊆ s₂) -> (s₂⊆s₃ : s₂ ⊆ s₃) -> s₁ ⊆ s₃
 ⊆-trans {s₁} {s₂} {s₃} s₁⊆s₂ s₂⊆s₃ x x∈s₁ with (s₂ x)
 ... | false = s₂⊆s₃ x (s₁⊆s₂ x x∈s₁)
 ... | true = s₂⊆s₃ x (s₁⊆s₂ x x∈s₁)
