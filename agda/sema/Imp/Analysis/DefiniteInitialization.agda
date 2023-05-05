------------------------------------------------------------------------
-- Definite initialization analysis for IMP and its properties
------------------------------------------------------------------------
module Imp.Analysis.DefiniteInitialization where 

open import Imp.Syntax using (Command ; Ident ; Store ; AExp ; BExp)
open import Imp.Semantics
open import Data.String
open import Data.Result renaming (bind to _>>=_)
open import Data.Bool
--

-- From Nipkow (10.1, citing the Java Language spec)
-- Each local variable [...] must have a definitely assigned value when any
-- access of its value occurs. [...] A compiler must carry out a specific conser-
-- vative flow analysis to make sure that, for every access of a local variable
-- [...] f, f is definitely assigned before the access; otherwise a compile-time
-- error must occur.



InitTable : Set
InitTable = Ident -> Bool 

emptyTable : InitTable
emptyTable = λ _ -> false

addInit : (i : Ident) -> (t : InitTable) -> InitTable 
addInit i t = λ x → if ( i == x ) then true else (t x)

private
 intersectInit : (t : InitTable) -> (t₁ : InitTable) -> InitTable 
 intersectInit t t₁ = λ id -> if (t id) then (t₁ id) else false

 dia-aexp : AExp -> InitTable -> Result {A = InitTable}
 dia-aexp (AExp.const x) t = Ok t
 dia-aexp (AExp.var x) t = if (t x) then (Ok t) else (Err (x ++ " is uninitialized!"))
 dia-aexp (AExp.plus x x₁) t = dia-aexp x t >>= λ t₁ -> dia-aexp x₁ t₁ >>= Ok
 dia-aexp (AExp.minus x x₁) t =  dia-aexp x t >>= λ t₁ -> dia-aexp x₁ t₁ >>= Ok
 dia-aexp (AExp.times x x₁) t = dia-aexp x t >>= λ t₁ -> dia-aexp x₁ t₁ >>= Ok
 dia-aexp (AExp.div x x₁) t = dia-aexp x t >>= λ t₁ -> dia-aexp x₁ t₁ >>= Ok
 
 dia-bexp : BExp -> InitTable -> Result {A = InitTable}
 dia-bexp BExp.true t = Ok t
 dia-bexp BExp.false t = Ok t
 dia-bexp (BExp.eq a₁ a₂) t = dia-aexp a₁ t >>= λ t₁ -> dia-aexp a₂ t₁ >>= Ok 
 dia-bexp (BExp.leq a₁ a₂) t = dia-aexp a₁ t >>= λ t₁ -> dia-aexp a₂ t₁ >>= Ok 
 dia-bexp (BExp.not x) t = dia-bexp x t 
 dia-bexp (BExp.and x x₁) t = dia-bexp x t >>= λ t₁ -> dia-bexp x₁ t₁ >>= Ok


dia : Command -> InitTable -> Result {A = InitTable} 
dia Command.skip t = Ok t 
dia (Command.assign id a) t = (dia-aexp a t) >>= λ t₁ -> Ok (addInit id t₁)
dia (Command.seq c c₁) t = dia c t >>= λ t₁ -> dia c₁ t₁ >>= Ok
dia (Command.ifelse b c c₁) t = dia-bexp b t >>= λ t₁ -> dia c t₁ >>= λ t₂ -> dia c₁ t₁ >>= λ t₃ -> Ok (intersectInit t₂ t₃)
dia (Command.while b c) t = dia-bexp b t >>= λ t₁ -> dia c t₁ >>= λ _ -> Ok t
-- ^ Note the conservative choice, we throw away the result of `dia c t₁` if it's not an error
