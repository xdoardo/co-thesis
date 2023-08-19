------------------------------------------------------------------------
-- The OR datatype 
------------------------------------------------------------------------
module Data.Or where 

data Or (A : Set) (B : Set) : Set where 
 left : A -> Or A B
 right : B -> Or A B
 both : A -> B -> Or A B

data XOr (A : Set) (B : Set) : Set where 
 left : A -> XOr A B
 right : B -> XOr A B
