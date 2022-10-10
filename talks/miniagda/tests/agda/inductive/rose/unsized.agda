{-# OPTIONS --sized-types #-}
{-# BUILTIN SIZE     Size     #-}  --  Size     : SizeUniv
{-# BUILTIN SIZELT   Size<_   #-}  --  Size<_   : ..Size → SizeUniv
{-# BUILTIN SIZESUC  ↑_       #-}  --  ↑_       : Size → Size
{-# BUILTIN SIZEINF  ∞        #-}  --  ∞        : Size

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

data List (A : Set) : Set where
  nil : List A 
  cons : A -> List A -> List A

mapList : {A : Set} -> {B : Set} -> (A -> B) -> List A -> List B
mapList f nil = nil 
mapList f (cons a x) = cons (f a) (mapList f x)

data Rose (A : Set) : Size → Set where
  rose : {i : Size} -> A -> List (Rose A i) → Rose A (↑ i)

mapRose : {A : Set} -> {B : Set} -> (A -> B) -> {i : Size} -> Rose A i -> Rose B i
mapRose f (rose a rs) = rose (f a) (mapList (mapRose f) rs)
