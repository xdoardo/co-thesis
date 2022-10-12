{-# OPTIONS --sized-types #-}
{-# BUILTIN SIZE     Size     #-}  --  Size     : SizeUniv
{-# BUILTIN SIZELT   Size<_   #-}  --  Size<_   : ..Size → SizeUniv
{-# BUILTIN SIZESUC  ↑_       #-}  --  ↑_       : Size → Size
{-# BUILTIN SIZEINF  ∞        #-}  --  ∞        : Size

data Nat : {i : Size} -> Set where
    zero : {i : Size} -> Nat {↑ i} 
    succ : {i : Size} -> Nat {i} -> Nat {↑ i}

monus : {i : Size} -> Nat {i} -> Nat {∞} -> Nat {i}
monus .{↑ j} (zero {j}) n = zero {j}
monus .{↑ j} (succ {j} x) (zero {∞}) = succ {j} x
monus .{↑ j} (succ {j} x) (succ {∞} y) = monus {j} x y

div : {i : Size} -> Nat {i} -> Nat {∞} -> Nat {i}
div .{↑ j} (zero {j}) y = zero {j}
div .{↑ j} (succ {j} x) y = succ (div {j} (monus {j} x y) y)
