------------------------------------------------------------------------
-- Terms for the λ-calculus
-----------------------------------------------------------------------
module Lambda.Syntax.Term where

open import Lambda.Syntax.Term.Core public

------------------------------------------------------------------------
-- Examples 
module _ where
 -- A non-terminating term.
 ω : Tm 0
 ω = t-lam (t-app (vr 0) (vr 0))
 
 Ω : Tm 0
 Ω = t-app ω ω 
