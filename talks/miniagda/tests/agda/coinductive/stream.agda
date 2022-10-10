{-# OPTIONS --guardedness #-}
open import Agda.Builtin.Nat 

record Stream (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    head : A
    tail : Stream A

open Stream public

repeat : Nat -> Stream Nat 
repeat x = x ∷ (repeat x) 

--repeat : Nat -> Stream Nat
--head (repeat x) = x
--tail (repeat x) = repeat x
--
--countFrom : Nat -> Stream Nat 
--head (countFrom x) = x 
--tail (countFrom x) = countFrom (suc x)
--
--open import Agda.Builtin.Equality
--
--_ : head (countFrom 0) ≡  0
--_ = refl
--
--_ : head (tail (countFrom 0)) ≡ 1
--_ = refl
