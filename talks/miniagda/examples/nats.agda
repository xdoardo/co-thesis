{-# OPTIONS --sized-types #-}
{-# BUILTIN SIZE     Size     #-}  --  Size     : SizeUniv
{-# BUILTIN SIZELT   Size<_   #-}  --  Size<_   : ..Size → SizeUniv
{-# BUILTIN SIZESUC  ↑_       #-}  --  ↑_       : Size → Size
{-# BUILTIN SIZEINF  ∞        #-}  --  ∞        : Size

data SNat : Size -> Set where
  zero : (i : Size) -> SNat (↑ i)
  succ : (i : Size) -> SNat (i) -> SNat (↑ i) 

minus : (j : Size) -> SNat j -> SNat ∞ -> SNat j
minus i (zero j) y = zero i
minus i x (zero .∞) = x
minus i (succ i x) (succ .∞ y) = minus i x y


open import Agda.Builtin.Equality
_ : minus _ (succ _ (zero _)) (succ _ (zero _ )) ≡ zero _
_ = refl

div : (i : Size) -> SNat i -> SNat ∞ -> SNat i
div (↑i) (zero i) y = zero i
div (↑i) (succ i x) y = succ i (div i (minus i x y) y)


_ : (div _ (succ _ (succ _ (succ _ (succ _ (zero _) )))) (succ _ (succ _ (zero _)))) ≡ (succ _ (succ _ (zero _)))
_ = refl
