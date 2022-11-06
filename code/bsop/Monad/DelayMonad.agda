---------------------------------------------------------------------------
-- The Delay monad
---------------------------------------------------------------------------

module Monad.DelayMonad where
 
open import Category.Monad
open import Agda.Builtin.Size 

mutual
  -- In Agda, the Delay type can be represented as a mutual definition of an
  -- inductive datatype and a coinductive record. The record ∞Delay is a
  -- coalgebra and one interacts with it by using its single observation
  -- (copattern) force. Once forced we get an element of the Delay datatype
  -- which we can pattern match on to see if the value is available now or
  -- later. If it is later then we get an element of ∞Delay which we can force
  -- again, and so forth.

  data Delay (i : Size) (A : Set) : Set where
    now : A -> Delay i A
    later : ∞Delay i A -> Delay i A

  record ∞Delay (i : Size) (A : Set) : Set where
    coinductive
    field force : {j : Size< i} -> Delay j A

-- The Delay monad is a monad. `now` is its `return`. The implementation of
-- `bind` follows a common scheme when working with Delay: we define two
-- mutually recursive functions, the first by pattern matching on Delay and the
-- second by copattern matching on ∞Delay.
module Bind where
mutual
  _>>=_ : ∀ {i A B} -> Delay i A -> (A -> Delay i B) -> Delay i B
  (now a) >>= f = f a
  (later ∞a) >>= f = later (∞a ∞>>= f)

  _∞>>=_ : ∀ {i A B} -> ∞Delay i A -> (A -> Delay i B) -> ∞Delay i B
  ∞Delay.force (a ∞>>= f) = (∞Delay.force a) >>= f

open Bind public
