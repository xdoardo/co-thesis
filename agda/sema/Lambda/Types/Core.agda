----------------------------------------------------------------------------------------------
-- Core definitions for the type system for the λ calculus
----------------------------------------------------------------------------------------------
module Lambda.Types.Core where 

open import Size
open import Codata.Sized.Thunk

data Ty : Size -> Set where 
  ⋆ : ∀ {i} -> Ty i
  _=>_ : ∀ {i} -> Thunk Ty i -> Thunk Ty i -> Ty i
