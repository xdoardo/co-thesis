------------------------------------------------------------------------
-- Functional semantics for expressions in Imp targeting the delay monad
------------------------------------------------------------------------
module Imp.Semantics.BigStep.Functional.Command where 

open import Size
open import Data.Bool
open import Imp.Syntax 
open import Codata.Sized.Delay
open import Codata.Sized.Thunk
open import Data.Maybe renaming (_>>=_ to _>>=m_)
open import Imp.Semantics.BigStep.Functional.Bool
open import Imp.Semantics.BigStep.Functional.Arith
open import Codata.Sized.Partial.Effectful renaming (bind to _>>=p_)
--

------------------------------------------------------------------------ 
-- An execution function `ceval s c` that runs the command `c` in initial store `s`
-- and returns the final store when `c` terminates, targeting the Partiality
-- Monad.
------------------------------------------------------------------------

mutual
 ceval-while : ∀ {i} (c : Command) (b : BExp) (s : Store) -> Thunk (Delay (Maybe Store)) i
 ceval-while c b s = λ where .force -> (ceval (while b c) s)
 
 ceval : ∀ {i} -> (c : Command) -> (s : Store) -> Delay (Maybe Store) i
 ceval skip s = now (just s)
 ceval (assign id a) s = now (aeval a s >>=m λ v -> just (update id v s))
 ceval (seq c c₁) s = ceval c s >>=p λ s' -> ceval c₁ s'
 ceval (ifelse b c c₁) s = now (beval b s) >>=p (λ bᵥ -> (if bᵥ then ceval c s else ceval c₁ s))
 ceval (while b c) s = now (beval b s) >>=p (λ bᵥ -> 
   if bᵥ 
   then (ceval c s >>=p  λ s -> later (ceval-while c b s))
   else now (just s)
  )
