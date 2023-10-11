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
open import Codata.Sized.FailingDelay.Relation.Binary.Convergence
---

-- Pure constant folding of boolean expressions
cpfold : Command -> Command
cpfold skip = skip
cpfold (assign id a) = assign id (apfold a) 
cpfold (seq c₁ c₂) = seq (cpfold c₁) (cpfold c₂)
cpfold (ifelse b c₁ c₂) = ifelse (bpfold b) (cpfold c₁) (cpfold c₂)
cpfold (while b c) = while (bpfold b) (cpfold c)

------------------------------------------------------------------------
-- Properties of constant folding 
------------------------------------------------------------------------
module _ where
 open import Codata.Sized.Delay
 open import Codata.Sized.Thunk
 open import Imp.Semantics.BigStep.Functional 
 open import Codata.Sized.Delay.WeakBisimilarity
 open import Relation.Binary.PropositionalEquality
 open import Imp.Semantics.BigStep.Functional.Properties
 open import Codata.Sized.FailingDelay.Effectful renaming (bind to bindᵖ)
 open import Codata.Sized.Delay.WeakBisimilarity.Relation.Binary.Equivalence using (≡=>≋)
  renaming (refl to prefl ; sym to psym ; trans to ptrans)
 open ≡-Reasoning 

 mutual
  cpfold-safe : ∀ {i} (c : Command) (s : Store) -> i ⊢ (ceval c s) ≋ (ceval (cpfold c) s)
  cpfold-safe skip s = prefl
  cpfold-safe (assign id a) s rewrite (apfold-safe a s) = prefl
  cpfold-safe (ifelse b cᵗ cᶠ) s rewrite sym (bpfold-safe b s)
   with (beval b s) 
  ... | nothing = prefl
  ... | just false = cpfold-safe cᶠ s 
  ... | just true = cpfold-safe cᵗ s 
  cpfold-safe {i} (seq c₁ c₂) s = bind-≋ (cpfold-safe c₁ s) (cpfold-safe c₂)
  cpfold-safe {i} (while b c) s rewrite sym (bpfold-safe b s)
   with (beval b s)
  ... | nothing = prefl
  ... | just false = prefl 
  ... | just true = bind-≋ (cpfold-safe c s) (λ s -> (later (cpfold-wsafe b c s)))

  private 
    cpfold-wsafe : ∀ {i} (b : BExp) (c : Command) (s : Store) 
     -> Thunk (λ i -> i ⊢ (force (ceval-while c b s)) ≋ (force (ceval-while (cpfold c) (bpfold b) s))) i
    force (cpfold-wsafe {i} b c s) {j}
     rewrite sym (bpfold-safe b s)
     with (beval b s)
    ... | nothing = prefl
    ... | just false = prefl 
    ... | just true 
     with (cpfold-safe c s) | (ceval c s) in eq-c | (ceval (cpfold c) s) in eq-cp
    ... | c≋cp | x | xᶠ rewrite eq-c rewrite eq-cp = unfold-w-safe c≋cp 

    unfold-w-safe : ∀ {i} {x x' : Delay (Maybe Store) ∞} {c b} (h : i ⊢ x ≋ x') 
     -> i ⊢ bindᵖ x (λ s -> later (ceval-while c b s)) ≋ bindᵖ x' (λ s -> later (ceval-while (cpfold c) (bpfold b) s))
    unfold-w-safe {i} {now (just x)} {now (just .x)} {c} {b} (now refl) = later (cpfold-wsafe b c x)
    unfold-w-safe {i} {now nothing} {now (just x)} (now ())
    unfold-w-safe {i} {now (just x)} {now nothing} (now ())
    unfold-w-safe {i} {now nothing} {now nothing} {c} {b} (now refl) = prefl
    unfold-w-safe {i} {now (just x)} {later x₁} {c} {b} (laterᵣ h) = laterᵣ (unfold-w-safe h)
    unfold-w-safe {i} {now nothing} {later x} {c} {b} (laterᵣ h) = laterᵣ (unfold-w-safe {b = b} h)
    unfold-w-safe {i} {later x} {x'} {c} {b} (laterₗ h) = laterₗ (unfold-w-safe h)
    unfold-w-safe {i} {later x} {.(later _)} {c} {b} (laterᵣ h) =  laterᵣ (unfold-w-safe h)
    unfold-w-safe {i} {later x} {.(later _)} {c} {b} (later h) = later (λ where .force -> unfold-w-safe (force h))
