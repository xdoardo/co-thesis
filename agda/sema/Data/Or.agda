module Data.Or where 

data Or (A : Set) (B : Set) : Set where 
 left : A -> Or A B
 right : B -> Or A B
 both : A -> B -> Or A B
