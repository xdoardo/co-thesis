{-# OPTIONS --sized-types #-}
data Nat : Set where 
  zero : Nat 
  succ : Nat -> Nat 

minus : Nat -> Nat -> Nat 
minus zero _ = zero
minus (succ x) zero = succ x
minus (succ x) (succ y) = minus x y


div : Nat -> Nat -> Nat 
div zero _ = zero 
div (succ x) y = succ (div (minus x y) y)
