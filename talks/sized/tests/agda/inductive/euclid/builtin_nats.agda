{-# OPTIONS --sized-types #-}
open import Agda.Builtin.Nat

minus : Nat -> Nat -> Nat 
minus zero _ = zero
minus (suc x) zero = suc x
minus (suc x) (suc y) = minus x y


-- Non accettata
div : Nat -> Nat -> Nat 
div zero _ = zero 
div (suc x) y = suc (div (minus x y) y)
