------------------------------------------------------------------------
-- Functional semantics for arithmetic expressions in Imp 
------------------------------------------------------------------------
module Imp.Semantics.BigStep.Functional.Command where

open import Imp.Syntax 
open import Data.Maybe
open import Data.Bool 
open import Imp.Semantics.BigStep.Functional.Arith
open import Imp.Semantics.BigStep.Functional.Bool

ceval : (c : Command) -> (s : Maybe Store) -> Maybe Store
ceval skip (just s) = just s
ceval (assign id a) (just s) = do 
 v <- aeval a s
 just (update id v s)
ceval (seq c c₁) (just s) = do 
 s₁ <- ceval c (just s)
 s₂ <- ceval c₁ (just s)
 just s₂
ceval (ifelse b c c₁) (just s) = do 
 b <- (beval b s) 
 if b then (ceval c (just s)) else (ceval c₁ (just s))
ceval (while b c) (just s) = do 
 b <- (beval b s)
 if b then (ceval c (just s) >>= λ s' -> (ceval c (just s'))) else (just s)
ceval  _ nothing = nothing
