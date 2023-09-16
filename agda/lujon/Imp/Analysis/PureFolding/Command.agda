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
open import Codata.Sized.Partial.Bisimilarity.Properties
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
  cpfold-sound : ∀ (c : Command) (s : Store) -> ∞ ⊢ (ceval c s) ≈ (ceval (cpfold c) s)
  cpfold-sound skip s rewrite (cpfold-skip) = nowj refl 
  cpfold-sound (assign id a) s = ≡=>≈ (cpfold-assign a id s)
  cpfold-sound (ifelse b cᵗ cᶠ) s = cpfold-if b cᵗ cᶠ s
  cpfold-sound (seq c₁ c₂) s = cpfold-seq c₁ c₂ s
  cpfold-sound (while b c) s = cpfold-while b c s 

  private 
   cpfold-skip : (cpfold skip) ≡ skip
   cpfold-skip = refl
 
   cpfold-assign : ∀ (a : AExp) (id : Ident) (s : Store) 
    -> (ceval (assign id a) s) ≡ (ceval (cpfold (assign id a)) s)
   cpfold-assign a id s 
    with (apfold-sound a s)
   ... | asound 
    with (aeval a s) in eq-av
   ... | nothing
    rewrite eq-av
    rewrite (sym asound)
    with (apfold a) in eq-ap
   ... | var id₁ rewrite eq-ap rewrite eq-av rewrite eq-av = refl
   ... | plus n n₁ rewrite eq-ap rewrite eq-av rewrite eq-av = refl
   cpfold-assign a id s | asound | just x 
    rewrite eq-av 
    rewrite (sym asound)
    with (apfold a) in eq-ap
   ... | var id₁ rewrite eq-ap rewrite eq-av rewrite eq-av = refl
   cpfold-assign a id s | asound | just x | plus n n₁ 
    rewrite eq-ap rewrite eq-av rewrite eq-av = refl
   cpfold-assign a id s | asound | just x | const n
    rewrite eq-ap rewrite eq-av rewrite eq-av 
    with asound 
   ... | refl = refl 

   cpfold-if : ∀ (b : BExp) (cᵗ cᶠ : Command) (s : Store) 
    -> ∞ ⊢ (ceval (ifelse b cᵗ cᶠ) s) ≈ (ceval (cpfold (ifelse b cᵗ cᶠ)) s)
   cpfold-if b cᵗ cᶠ s
    with (bpfold-sound b s)
   ... | bsound   
    with (beval b s) in eq-b
   ... | nothing 
    rewrite eq-b 
    rewrite (sym bsound) 
    with (bpfold b) in eq-bp
   ... | le a₁ a₂ rewrite eq-bp rewrite eq-b rewrite eq-b = nown
   ... | not n rewrite eq-bp rewrite eq-b rewrite eq-b = nown
   ... | and n n₁ rewrite eq-bp rewrite eq-b rewrite eq-b = nown
   cpfold-if b cᵗ cᶠ s | bsound | just false rewrite eq-b 
    rewrite eq-b 
    rewrite (sym bsound) 
    with (bpfold b) in eq-bp
   ... | const false rewrite eq-bp rewrite eq-b rewrite eq-b = cpfold-sound cᶠ s 
   ... | le a₁ a₂ rewrite eq-bp rewrite eq-b rewrite eq-b = cpfold-sound cᶠ s 
   ... | not n  rewrite eq-bp rewrite eq-b rewrite eq-b = cpfold-sound cᶠ s 
   ... | and n n₁ rewrite eq-bp rewrite eq-b rewrite eq-b = cpfold-sound cᶠ s 
   cpfold-if b cᵗ cᶠ s | bsound | just true rewrite eq-b
    rewrite eq-b 
    rewrite (sym bsound) 
    with (bpfold b) in eq-bp
   ... | const true rewrite eq-bp rewrite eq-b rewrite eq-b = cpfold-sound cᵗ s 
   ... | le a₁ a₂ rewrite eq-bp rewrite eq-b rewrite eq-b = cpfold-sound cᵗ s 
   ... | not n  rewrite eq-bp rewrite eq-b rewrite eq-b = cpfold-sound cᵗ s 
   ... | and n n₁ rewrite eq-bp rewrite eq-b rewrite eq-b = cpfold-sound cᵗ s 

   cpfold-seq : ∀ (c₁ c₂ : Command) (s : Store) 
    -> ∞ ⊢ (ceval (seq c₁ c₂) s) ≈ (ceval (cpfold (seq c₁ c₂)) s)
   cpfold-seq c₁ c₂ s = ? 
   
   cpfold-while : ∀ (b : BExp) (c : Command) (s : Store) 
    -> ∞ ⊢ (ceval (while b c) s) ≈ (ceval (cpfold (while b c)) s)
   cpfold-while b c s = ?
