module Codata.Sized.Delay.Examples where 
 open import Size
 open import Data.Integer
 open import Codata.Sized.Delay 
 open import Codata.Sized.Thunk
 open import Relation.Binary.PropositionalEquality


 comp-a : ∀ {i} -> Delay ℤ i
 comp-a = now 0ℤ

 comp-b : ∀ {i} -> Delay ℤ i
 comp-b = later λ where .force -> now 0ℤ

-- comp-a≡comp-b : comp-a ≡ comp-b 
-- comp-a≡comp-b = refl
