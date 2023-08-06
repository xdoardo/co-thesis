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
 open import Relation.Binary.PropositionalEquality
 open import Imp.Semantics.BigStep.Functional 
 open import Codata.Sized.Delay
 open import Codata.Sized.Partial.Effectful renaming (bind to bindᵖ)
 open ≡-Reasoning 

 
 -- Folding preserves semantics.
 cpfold-sound : ∀ c s  -> (ceval c s ≡ ceval (cpfold c) s)
 cpfold-sound skip s = refl
 cpfold-sound (assign id a) s rewrite (apfold-sound a s) 
  with (aeval a s) in eq-aeval | (apfold a) in eq-apfold
 ... | just x | const n rewrite eq-apfold  = refl 
 ... | just x | var id₁ rewrite eq-apfold = refl
 ... | just x | plus v v₁ rewrite eq-apfold = refl
 ... | nothing | const n rewrite eq-aeval = refl
 ... | nothing | var id₁ rewrite eq-aeval =  refl
 ... | nothing | plus v v₁ rewrite eq-aeval = refl
 cpfold-sound (seq c₁ c₂) s rewrite sym (cpfold-sound c₁ s) with (ceval c₁ s)
 ... | now (just x) rewrite (cpfold-sound c₂ x) = refl
 ... | now nothing = refl
 ... | later x = ? 
 cpfold-sound (ifelse b cᵗ cᶠ) s rewrite (bpfold-sound b s) with (bpfold b) in eq-bfold
 ... | const true rewrite eq-bfold rewrite (cpfold-sound cᵗ s) = refl
 ... | const false rewrite eq-bfold rewrite (cpfold-sound cᶠ s) = refl
 ... | le a₁ a₂ rewrite (cpfold-sound cᵗ s) rewrite (cpfold-sound cᶠ s) = refl
 ... | not b' rewrite (cpfold-sound cᵗ s) rewrite (cpfold-sound cᶠ s) = refl
 ... | and b' b'' rewrite (cpfold-sound cᵗ s) rewrite (cpfold-sound cᶠ s) = refl
 cpfold-sound (while b c) s rewrite sym (cpfold-sound c s) with (beval b s) in eq-beval
 ... | nothing rewrite (bpfold-sound b s) rewrite eq-beval = refl 
 ... | just false rewrite (bpfold-sound b s) rewrite eq-beval = refl
 ... | just true rewrite (bpfold-sound b s) = ? 
