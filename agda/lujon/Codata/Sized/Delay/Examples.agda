module Codata.Sized.Delay.Examples where 
 open import Size
 open import Data.Integer
 open import Codata.Sized.Thunk
 open import Relation.Binary.PropositionalEquality
 open import Codata.Sized.Delay renaming (bind to _>>=_)


 comp-a : ∀ {i} -> Delay ℤ i
 comp-a = now 0ℤ

 comp-b : ∀ {i} -> Delay ℤ i
 comp-b = later λ where .force -> now 0ℤ

-- comp-a≡comp-b : comp-a ≡ comp-b 
-- comp-a≡comp-b = refl


 module MonadLaws {a} {A : Set a} {b} {B : Set b} {c} {C : Set c}  where 

  open import Codata.Sized.Delay.WeakBisimilarity
  open import Codata.Sized.Delay.WeakBisimilarity.Relation.Binary.Equivalence 
   using () renaming (refl to prefl)

  left-identity : ∀ {i} (x : A) (f : A -> Delay B i) -> (now x) >>= f ≡ f x
  left-identity {i} x f = _≡_.refl

  right-identity : ∀ {i} (x : Delay A ∞) -> i ⊢ x >>= now ≋ x
  right-identity (now x) = now _≡_.refl
  right-identity {i} (later x) = later (λ where .force -> right-identity (force x))

  associativity : ∀ {i} {x : Delay A ∞} {f : A -> Delay B ∞} {g : B -> Delay C ∞} 
   -> i ⊢ (x >>= f) >>= g ≋ x >>= λ y -> (f y >>= g) 
  associativity {i} {now x} {f} {g} with (f x)
  ... | now x₁ = prefl 
  ... | later x₁ = prefl 
  associativity {i} {later x} {f} {g} = later (λ where .force -> associativity {x = force x}) 
