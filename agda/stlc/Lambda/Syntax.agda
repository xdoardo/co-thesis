------------------------------------------------------------------------
-- The syntax of a λ-calculus with constants
------------------------------------------------------------------------
module Lambda.Syntax where

open import Lambda.Syntax.Term public
open import Lambda.Syntax.Value public
---

-- A non-terminating term.
ω : Tm 0
ω = t-lam (t-app (vr 0) (vr 0))

Ω : Tm 0
Ω = t-app ω ω 
