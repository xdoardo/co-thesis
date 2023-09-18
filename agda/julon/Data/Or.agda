------------------------------------------------------------------------
-- The OR datatype 
------------------------------------------------------------------------
module Data.Or where 

open import Level

data Or {a} {b} (A : Set a) (B : Set b) : Set (a ⊔ b) where 
 left : A -> Or A B
 right : B -> Or A B
 both : A -> B -> Or A B

data XOr {a} {b} (A : Set a) (B : Set b) : Set (a ⊔ b) where 
 left : A -> XOr A B
 right : B -> XOr A B
