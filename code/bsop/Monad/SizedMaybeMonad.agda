---------------------------------------------------------------------------
-- The sized Maybe monad
---------------------------------------------------------------------------

module Monad.SizedMaybeMonad where 

open import Agda.Builtin.Size 
open import Category.Monad
open import Function 

data Maybe (i : Size) (A : Set) : Set where 
  nothing : Maybe i A
  just : A -> Maybe i A

module Bind where
  _>>=_ : ∀ {i A B} -> Maybe i A -> (A -> Maybe i B) -> Maybe i B
  (nothing) >>= f = nothing
  (just a) >>= f = f a 

open Bind public

--maybeMonad : ∀ {i} -> RawMonad (Maybe {i})
--maybeMonad {i} = record 
--  {
--    return = just 
--    ; _>>=_ = _>>=_ {i}
--  } where open Bind
--
--
--maybe : {A : Set} {B : Maybe A → Set} →
--        ((x : A) → B (just x)) → B nothing → (x : Maybe A) → B x
--maybe j n (just x) = j x
--maybe j n nothing  = n
--
--maybeMonadT : RawMonadT (_∘ Maybe)
--maybeMonadT M = record
--  { return = M.return ∘ just
--  ; _>>=_  = λ m f → m M.>>= maybe f (M.return nothing)
--  }
--  where module M = RawMonad M
