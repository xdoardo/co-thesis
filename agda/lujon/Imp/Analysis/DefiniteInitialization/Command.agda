------------------------------------------------------------------------
-- Definite initialization for commands of Imp
------------------------------------------------------------------------
module Imp.Analysis.DefiniteInitialization.Command where

open import Data.Maybe 
open import Data.Bool
open import Data.Integer
open import Imp.Syntax.Ident 
open import Imp.Syntax using (Store ; Command ; Ident)
open import Imp.Analysis.DefiniteInitialization.Arith
open import Imp.Analysis.DefiniteInitialization.Bool
---

open Command
---


dia : Command -> Store -> Maybe Store
dia skip t = just t 
dia (assign id a) t = (dia-aexp a t) >>= λ t₁ -> just (update id 0ℤ t₁)
dia (seq c c₁) t = dia c t >>= λ t₁ -> dia c₁ t₁ >>= just
dia (ifelse b c c₁) t = dia-bexp b t >>= λ t₁ -> dia c t₁ >>= λ t₂ -> dia c₁ t₁ >>= λ t₃ -> just (merge t₂ t₃)
dia (while b c) t = dia-bexp b t >>= λ t₁ -> dia c t₁ >>= λ _ -> just t
-- ^ Note the conservative choice, we throw away the result of `dia c t₁` if it's not an error
--

------------------------------------------------------------------------
-- Properties of definite initialization for commands
------------------------------------------------------------------------
module _ where 
 open import Data.Maybe
 open import Data.Product 
 open import Data.Integer
 open import Codata.Sized.Delay
 open import Imp.Semantics.Functional
 open import Relation.Binary.PropositionalEquality
 open ≡-Reasoning
 --- 

  

 -- For every arithmetic expression a and store s, if evaluating a in s results
 -- in nothing then the definite initialization of a in s results in nothing as
 -- well. 
 dia-nothing : ∀ (c : Command) (s : Store) -> (eval-nothing : ceval c s ≡ (now nothing)) -> dia c s ≡ nothing
 dia-nothing (assign id a) s eval-nothing with (aeval a s) in eq-aeval
 ... | nothing with (dia-aexp a s) in eq-aexp
 ... | just x rewrite (sym eq-aexp) = let 
  is-nothing = sym(dia-aexp-nothing a s eq-aeval) 
  bot = begin nothing ≡⟨ is-nothing ⟩ dia-aexp a s ≡⟨ eq-aexp ⟩ just x ∎ 
  in ?
 ... | nothing = refl
 dia-nothing (seq c c₁) s eval-nothing = {! !}
 dia-nothing (ifelse b c c₁) s eval-nothing = {! !}
 dia-nothing (while b c) s eval-nothing = {! !}
