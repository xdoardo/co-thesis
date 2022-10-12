{-# OPTIONS --guardedness #-}
open import Agda.Builtin.Nat 
open import Agda.Builtin.Equality

record NatStream : Set where
  coinductive
  constructor _::_
  field
    head : Nat
    tail : NatStream

open NatStream public

countFrom : Nat -> NatStream 
head (countFrom x) = x 
tail (countFrom x) = countFrom (x + 1)

repeat : Nat -> NatStream
head (repeat x) = x 
tail (repeat x) = repeat x

repeatF : (NatStream -> NatStream) -> Nat -> NatStream
head (repeatF _ x) = x 
tail (repeatF F x) = F (repeatF F x)
