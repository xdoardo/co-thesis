{-# OPTIONS --copatterns --sized-types #-}
{-# BUILTIN SIZE     Size     #-}  --  Size     : SizeUniv
{-# BUILTIN SIZELT   Size<_   #-}  --  Size<_   : ..Size → SizeUniv
{-# BUILTIN SIZESUC  ↑_       #-}  --  ↑_       : Size → Size
{-# BUILTIN SIZEINF  ∞        #-}  --  ∞        : Size


mutual
  data Delay (i : Size) (A : Set) : Set where
    now : A → Delay i A
    later : Delay' i A → Delay i A

  record Delay' (i : Size) (A : Set) : Set where
    coinductive
    field
      force : {j : Size< i} → Delay j A

open Delay public 
open Delay' public

never : {i : Size} -> {A : Set} -> Delay' i A
force (never {i} {A}) {j} = later (never {j} {A})
