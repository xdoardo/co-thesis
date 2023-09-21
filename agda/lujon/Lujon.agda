module Lujon where 

-- [misc]: Data 
open import Data.And 
open import Data.Or
open import Data.CharacteristicFunction 

-- Part 1: Weak bisimilarity
open import Codata.Sized.Delay.WeakBisimilarity
open import Codata.Sized.Delay.WeakBisimilarity.Relation.Binary.Equivalence

-- Part 2: Trivial combinators for Delay + Maybe
open import Codata.Sized.FailingDelay.Effectful
open import Codata.Sized.FailingDelay.Relation.Binary.Convergence

-- Part 3: Imp
open import Imp.Syntax
open import Imp.Semantics.BigStep.Functional
open import Imp.Semantics.BigStep.Functional.Properties
open import Imp.Analysis.DefiniteInitialization
-- open import Imp.Analysis.PureFolding

module _ where 
 open import Size
 open import Data.Integer
 open import Codata.Sized.Thunk
 open import Codata.Sized.Delay
 open import Relation.Binary.PropositionalEquality

 t-failing : ∀ {i} {ℓ} {A : Set ℓ} -> never {A = A} {i = i} ≡ never {A = A} {i = i} 
 t-failing = _≡_.refl

 t : ∀ {i} {ℓ} {A : Set ℓ} -> i ⊢ (never {A = A}) ≋ (never {A = A})
 t = later λ where .force -> t

 data DelayStream {a} (A : Set a) (i : Size) : Set a where 
   _::_ : A -> Thunk (DelayStream A) i -> DelayStream A i

 x : ∀ {i} -> DelayStream ℤ i 
 x = 0ℤ :: λ where .force -> x 

 head : ∀ {a} {A : Set a} -> (s : DelayStream A ∞) -> A
 head (v :: _) = v

 tail : ∀ {a} {A : Set a} -> (s : DelayStream A ∞) -> DelayStream A ∞
 tail (_ :: s) = force s

 obs : head (tail (tail (tail (tail x)))) ≡ 0ℤ
 obs = _≡_.refl
