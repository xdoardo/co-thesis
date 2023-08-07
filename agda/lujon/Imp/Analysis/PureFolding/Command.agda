------------------------------------------------------------------------
-- Pure constant folding (no constant propagation) for commands of Imp
------------------------------------------------------------------------
module Imp.Analysis.PureFolding.Command where

open import Data.Bool renaming (not to lnot)
open import Data.Unit
open import Data.Maybe
open import Imp.Syntax
open import Data.Integer
open import Imp.Analysis.PureFolding.Arith
open import Imp.Analysis.PureFolding.Bool
open import Data.Integer.Properties as ℤ-Properties
open import Data.Nat using () renaming (suc to ℕ-suc)
---

-- Pure constant folding of boolean expressions
cpfold : Command -> Command
cpfold skip = skip
cpfold (assign id a) with (apfold a)
... | const n = assign id (const n) 
... | a = assign id a 
cpfold (seq c₁ c₂) = seq (cpfold c₁) (cpfold c₂)
cpfold (ifelse b c₁ c₂) with (bpfold b) 
... | const false = cpfold c₂ 
... | const true = cpfold c₁ 
... | b'  = ifelse b' (cpfold c₁) (cpfold c₂)
cpfold (while b c) = while (bpfold b) (cpfold c)

------------------------------------------------------------------------
-- Properties of constant folding 
------------------------------------------------------------------------
module _ where
 open import Codata.Sized.Delay
 open import Codata.Sized.Thunk
 open import Imp.Semantics.BigStep.Functional 
 open import Codata.Sized.Partial.Bisimilarity
 open import Relation.Binary.PropositionalEquality
 open import Codata.Sized.Partial.Effectful renaming (bind to bindᵖ)
 open ≡-Reasoning 

 
 -- Folding preserves semantics.
 cpfold-sound : ∀ c s {i} -> (i ⊢ ceval c s ≈ ceval (cpfold c) s)
 cpfold-sound skip s = nowj refl
 cpfold-sound (assign id a) s with (aeval a s) in eq-aeval
 ... | just v rewrite (apfold-sound a s) rewrite eq-aeval = {! !}
 ... | nothing = ?
 cpfold-sound (seq c c₁) s = ? 
 cpfold-sound (ifelse b c c₁) s = ?
 cpfold-sound (while b c) s = ?
