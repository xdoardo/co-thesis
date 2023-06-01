------------------------------------------------------------------------
-- The And datatype 
------------------------------------------------------------------------
open import Agda.Primitive using (_⊔_)

module Data.And {a} {b} where 

data And (A : Set a) (B : Set b) : Set (a ⊔ b) where 
 both : A -> B -> And A B
