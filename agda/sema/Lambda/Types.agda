----------------------------------------------------------------------------------------------
-- Type system for the λ calculus with constants
----------------------------------------------------------------------------------------------
module Lambda.Types where 

open import Size
open import Data.Nat 
open import Data.Fin using (Fin)
open import Lambda.Syntax
open import Codata.Sized.Thunk

data Ty : Set where 
  * : Ty 
  _=>_ : Ty -> Ty -> Ty


