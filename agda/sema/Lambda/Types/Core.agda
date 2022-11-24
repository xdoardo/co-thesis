----------------------------------------------------------------------------------------------
-- Core definitions for the type system for the λ calculus
----------------------------------------------------------------------------------------------
module Lambda.Types.Core where 

open import Size
open import Data.Nat
open import Data.Vec
open import Codata.Sized.Thunk

data Ty : Size -> Set where 
  ⋆ : ∀ {i} -> Ty i
  _=>_ : ∀ {i} -> Thunk Ty i -> Thunk Ty i -> Ty i


-- Type context are defined just as syntax term environments
Ctxt : ℕ -> {Size} → Set
Ctxt n {i} = Vec (Ty i) n
