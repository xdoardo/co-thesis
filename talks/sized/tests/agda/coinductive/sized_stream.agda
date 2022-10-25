{-# OPTIONS --copatterns --sized-types #-}
{-# BUILTIN SIZE     Size     #-}  --  Size     : SizeUniv
{-# BUILTIN SIZELT   Size<_   #-}  --  Size<_   : ..Size → SizeUniv
{-# BUILTIN SIZESUC  ↑_       #-}  --  ↑_       : Size → Size
{-# BUILTIN SIZEINF  ∞        #-}  --  ∞        : Size

record Stream {A : Set} {i : Size} : Set where 
  coinductive
  field
    head : A
    tail : {j : Size< i} -> Stream {A} {j}

open Stream public 

repeat : {A : Set} -> {i : Size} -> A -> Stream {A} {i}
head (repeat {A} {i} x) = x
tail (repeat {A} {i} x) {j} = repeat {A} {j} x

map : {A : Set} -> {B : Set} -> {i : Size} -> (A -> B) -> Stream {A} {i} -> Stream {B} {i}
head (map {A} {B} {i} f s) = f (head s)
tail (map {A} {B} {i} f s) {j} = map {A} {B} {j} f (tail s)
