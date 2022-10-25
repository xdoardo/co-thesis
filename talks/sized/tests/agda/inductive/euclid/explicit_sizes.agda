{-# OPTIONS --sized-types #-}
{-# BUILTIN SIZE     Size     #-}  --  Size     : SizeUniv
{-# BUILTIN SIZELT   Size<_   #-}  --  Size<_   : ..Size → SizeUniv
{-# BUILTIN SIZESUC  ↑_       #-}  --  ↑_       : Size → Size
{-# BUILTIN SIZEINF  ∞        #-}  --  ∞        : Size

data Nat : {i : Size} -> Set where
    zero : {i : Size} -> Nat {↑ i} 
    succ : {i : Size} -> Nat {i} -> Nat {↑ i}

monus : {i : Size} -> Nat {i} -> Nat -> Nat {i}
monus .{↑ j} (zero {j}) n = zero {j}
monus .{↑ j} (succ {j} x) (zero) = succ {j} x
monus .{↑ j} (succ {j} x) (succ y) = monus {j} x y

monus1 : {i : Size} -> Nat {i} -> Nat -> Nat {i}
monus1 (zero ) n = zero
monus1 (succ x) (zero) = succ  x
monus1 (succ x) (succ y) = monus  x y



open import Agda.Builtin.Equality

_ : (monus (succ (succ zero)) (succ zero)) ≡ (succ zero) 
_ = refl

_ : (monus1 (succ (succ zero)) (succ zero)) ≡ (succ zero) 
_ = refl


div : {i : Size} -> Nat {i} -> Nat {∞} -> Nat {i}
div .{↑ j} (zero {j}) y = zero {j}
div .{↑ j} (succ {j} x) y = succ (div {j} (monus {j} x y) y)

div1 : {i : Size} -> Nat {i} -> Nat {∞} -> Nat {i}
div1 (zero ) y = zero
div1 (succ x) y = succ (div1 (monus1  x y) y)
