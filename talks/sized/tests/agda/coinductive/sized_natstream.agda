{-# OPTIONS --copatterns --sized-types #-}
{-# BUILTIN SIZE     Size     #-}  --  Size     : SizeUniv
{-# BUILTIN SIZELT   Size<_   #-}  --  Size<_   : ..Size → SizeUniv
{-# BUILTIN SIZESUC  ↑_       #-}  --  ↑_       : Size → Size
{-# BUILTIN SIZEINF  ∞        #-}  --  ∞        : Size

open import Agda.Builtin.Nat 

record NatStream {i : Size} : Set where
  coinductive
  constructor _::_
  field
    head : Nat
    tail : {j : Size< i} → NatStream {j}

open NatStream public

countFrom : {j : Size} -> Nat -> NatStream {j}
head (countFrom {_} x) = x
tail (countFrom {j} x) {i}  = countFrom {i} (x + 1)

repeat : {j : Size} -> Nat -> NatStream {j}
head (repeat {_} x) = x 
tail (repeat {i} x) {j} = repeat {j} x

repeatF : {i : Size}  -> Nat -> ({j : Size< i} -> NatStream {j} -> NatStream {j})  -> NatStream {i}
head (repeatF n _) = n 
tail (repeatF n f) = f (repeatF n f)
