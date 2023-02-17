open import Data.Nat 
open import Data.Bool 
open import Data.String 
open import Agda.Primitive 


-- data List {A : Set} : Set where
--   []   : List 
--   _::_ : A -> List {A} -> List

-- This won't work! Set₁ != Set
-- list : List 
-- list = ℕ :: (Bool :: (String :: []))

data UList {ℓ} {A : Set ℓ} : Set ℓ where 
 [] : UList 
 _::_ : A -> UList {ℓ} {A} -> UList {ℓ} {A}

list : UList {lsuc lzero} {Set}
list = ℕ :: (Bool :: (String :: []))
