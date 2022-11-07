---------------------------------------------------------------------------
-- The Delay monad
---------------------------------------------------------------------------

module Data.Delay where
 
open import Agda.Builtin.Size 
---

mutual

  data Delay {i : Size} (A : Set) : Set where
    now : A -> Delay {i} A
    later : ∞Delay {i} A -> Delay {i} A

  record ∞Delay {i : Size} (A : Set) : Set where
    coinductive
    field force : {j : Size< i} -> Delay {j} A
