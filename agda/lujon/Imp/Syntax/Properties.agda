------------------------------------------------------------------------
-- Properties of the syntax of IMP
------------------------------------------------------------------------
module Imp.Syntax.Properties where 

open import Data.Or
open import Data.Maybe
open import Imp.Syntax
open import Data.Integer
open import Relation.Binary.PropositionalEquality
---


------------------------------------------------------------------------
-- Properties and lemmas of arithmetic expressions
------------------------------------------------------------------------
module _ where 
 
 --- Honestly, I ** HOPE ** these are utterly unnecessary. Otherwise, Agda 
 --- has a HUGE problem!
 
 -- Two `vars` are propositionally equivalent iff their `id`s are the same. 
 eq-var-id : ∀ {id₁ id₂} (h : var id₁ ≡ var id₂) -> id₁ ≡ id₂
 eq-var-id refl = refl

 -- Two `const` are propositionally equivalent iff their `v`s are the same. 
 eq-const-v : ∀ {v₁ v₂} (h : const v₁ ≡ const v₂) -> v₁ ≡ v₂
 eq-const-v refl = refl
