------------------------------------------------------------------------
-- Pure constant folding (no constant propagation) for commands of Imp
------------------------------------------------------------------------
module Imp.Analysis.PureFolding.Command where

open import Size
open import Data.Or
open import Data.Unit
open import Data.Maybe
open import Imp.Syntax
open import Data.Product
open import Data.Integer
open import Function using (case_of_)
open import Imp.Analysis.PureFolding.Bool
open import Imp.Analysis.PureFolding.Arith
open import Data.Bool renaming (not to lnot)
open import Data.Integer.Properties as ℤ-Properties
open import Data.Nat using () renaming (suc to ℕ-suc)
open import Codata.Sized.Partial.Relation.Binary.Convergence
open import Codata.Sized.Partial.Bisimilarity.Relation.Binary.Equivalence renaming (refl to prefl ; sym to psym)
---

-- Pure constant folding of boolean expressions
cpfold : Command -> Command
cpfold skip = skip
cpfold (assign id a) with (apfold a)
... | const n = assign id (const n) 
... | _ = assign id a 
cpfold (seq c₁ c₂) = seq (cpfold c₁) (cpfold c₂)
cpfold (ifelse b c₁ c₂) with (bpfold b) 
... | const false = cpfold c₂ 
... | const true = cpfold c₁ 
... | _ = ifelse b (cpfold c₁) (cpfold c₂)
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
 open import Imp.Semantics.BigStep.Functional.Properties
 open import Codata.Sized.Partial.Effectful renaming (bind to bindᵖ)
 open ≡-Reasoning 

 
 mutual 
  -- Folding preserves semantics.
  cpfold-sound : ∀ c s -> (∞ ⊢ ceval c s ≈ ceval (cpfold c) s)
  cpfold-sound skip s = nowj refl
  cpfold-sound (assign id a) s with (apfold-sound a s) | (apfold a) in eq-apfold 
  ... | eq-ev-ap | const n rewrite eq-apfold rewrite eq-ev-ap = (≡=>≈ refl)
  ... | eq-ev-ap | var id₁ rewrite eq-apfold rewrite eq-ev-ap = (≡=>≈ refl)
  ... | eq-ev-ap | plus v v₁ rewrite eq-apfold rewrite eq-ev-ap = (≡=>≈ refl)
  cpfold-sound (ifelse b cᵗ cᶠ) s with (bpfold-sound b s)
  ... | eq-bev-bp with (beval b s) in eq-beval-b 
  ... | nothing with (bpfold b) in eq-bpfold
  ... | le a₁ a₂ rewrite eq-bpfold rewrite eq-beval-b = nown
  ... | not n rewrite eq-bpfold rewrite eq-beval-b = nown
  ... | and n n₁ rewrite eq-bpfold rewrite eq-beval-b = nown
  cpfold-sound (ifelse b cᵗ cᶠ) s | eq-bev-bp | just false 
   rewrite eq-beval-b 
   with (bpfold b) in eq-bpfold
  ... | const b₁ with (eq-bev-bp) 
  ... | refl with (cpfold (ifelse b cᵗ cᶠ))
  ... | _ = cpfold-sound cᶠ s
  cpfold-sound (ifelse b cᵗ cᶠ) s | eq-bev-bp | just false | le a₁ a₂ with (cpfold (ifelse b cᵗ cᶠ)) 
  ... | n rewrite eq-beval-b rewrite eq-beval-b = cpfold-sound cᶠ s
  cpfold-sound (ifelse b cᵗ cᶠ) s | eq-bev-bp | just false | not a with (cpfold (ifelse b cᵗ cᶠ)) 
  ... | n rewrite eq-beval-b rewrite eq-beval-b = cpfold-sound cᶠ s
  cpfold-sound (ifelse b cᵗ cᶠ) s | eq-bev-bp | just false | and a a₁ with (cpfold (ifelse b cᵗ cᶠ)) 
  ... | n rewrite eq-beval-b rewrite eq-beval-b = cpfold-sound cᶠ s
  cpfold-sound (ifelse b cᵗ cᶠ) s | eq-bev-bp | just true rewrite eq-beval-b
    with (bpfold b) in eq-bpfold
  ... | const b₁ with (eq-bev-bp) 
  ... | refl with (cpfold (ifelse b cᵗ cᶠ))
  ... | _ = cpfold-sound cᵗ s
  cpfold-sound (ifelse b cᵗ cᶠ) s | eq-bev-bp | just true | le a₁ a₂ with (cpfold (ifelse b cᵗ cᶠ)) 
  ... | n rewrite eq-beval-b rewrite eq-beval-b = cpfold-sound cᵗ s
  cpfold-sound (ifelse b cᵗ cᶠ) s | eq-bev-bp | just true | not a with (cpfold (ifelse b cᵗ cᶠ)) 
  ... | n rewrite eq-beval-b rewrite eq-beval-b = cpfold-sound cᵗ s
  cpfold-sound (ifelse b cᵗ cᶠ) s | eq-bev-bp | just true | and a a₁ with (cpfold (ifelse b cᵗ cᶠ)) 
  ... | n rewrite eq-beval-b rewrite eq-beval-b = cpfold-sound cᵗ s 
  cpfold-sound (seq c₁ c₂) s with  (cpfold-sound c₁ s)
  ... | c₁≈ = ? 
  cpfold-sound (while b c) s with  (cpfold-sound c s)
  ... | c≈ = ?
