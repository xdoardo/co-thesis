------------------------------------------------------------------------
-- The indicator function datatype 
------------------------------------------------------------------------
open import Data.Bool
---

module Data.IndicatorFunction {a} (A : Set a) (_==_ : A -> A -> Bool) where

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
s₁ ⊆ s₂ = ∀ x -> (s₁ x ≡ true) -> s₂ x ≡ true
