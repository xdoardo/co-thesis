{-# OPTIONS --sized-types #-}
{-# BUILTIN SIZE     Size     #-}  --  Size     : SizeUniv
{-# BUILTIN SIZELT   Size<_   #-}  --  Size<_   : ..Size → SizeUniv
{-# BUILTIN SIZESUC  ↑_       #-}  --  ↑_       : Size → Size
{-# BUILTIN SIZEINF  ∞        #-}  --  ∞        : Size

data SNat : Size -> Set where
  zero : {i : Size} -> SNat (↑ i)
  succ : {i : Size} -> SNat (i) -> SNat (↑ i) 

minus : {j : Size} -> SNat j -> SNat ∞ -> SNat j
minus  zero y = zero
minus  x zero  = x
minus  (succ x) (succ y) = minus x y


open import Agda.Builtin.Equality
_ : minus (succ zero) (succ zero) ≡ zero
_ = refl

div : {i : Size} -> SNat i -> SNat ∞ -> SNat i
div zero y = zero
div (succ x) y = succ (div (minus x y) y)


_ : (div  (succ  (succ  (succ  (succ  zero)))) (succ  (succ zero))) ≡ (succ  (succ  (zero )))
_ = refl
