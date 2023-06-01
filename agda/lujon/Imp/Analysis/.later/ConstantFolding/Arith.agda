------------------------------------------------------------------------
-- Constant folding for arithmetic expressions of Imp
------------------------------------------------------------------------
module Imp.Analysis.ConstantFolding.Arith where

open import Data.Unit
open import Data.Maybe
open import Data.Integer
open import Imp.Syntax.Ident
open import Imp.Syntax.Arith
open import Data.Integer.Properties as ℤ-Properties
open import Data.Nat using () renaming (suc to ℕ-suc)
---

-- Constant folding (and constant propagation) of arithmetic expressions
afold : (a : AExp) -> (s : Store) -> AExp
afold (const x) _ = const x 
afold (var id) s with (s id)  
... | just v = const v
... | nothing = var id
afold (plus a₁ a₂) s with (afold a₁ s) | (afold a₂ s)
... | const v₁ | const v₂ = const (v₁ + v₂)
... | a₁' | a₂' = plus a₁' a₂'

------------------------------------------------------------------------
-- Properties of constant folding 
------------------------------------------------------------------------
module _ where
 open import Relation.Binary.PropositionalEquality
 open import Imp.Semantics.Functional 
 open ≡-Reasoning 

 -- Folding is idempotent under the same store. 
 afold-idem : ∀ a s -> afold a s ≡ afold (afold a s) s
 afold-idem (const n) _ = refl
 afold-idem (var id) s with (s id) in eq-id
 ... | just x = refl
 ... | nothing rewrite eq-id = refl
 afold-idem (plus a a₁) s with (afold-idem a s) | (afold-idem a₁ s)
 ... | a-idem | a₁-idem with (afold a s) in eq-a | (afold a₁ s) in eq-a₁
 ... | const n | const n₁ = refl
 ... | const n | var id with (s id) 
 ... | nothing = refl
 afold-idem (plus a a₁) s | a-idem | a₁-idem | const n | plus a₁' a₁'' 
  rewrite (eq-a) rewrite (eq-a₁) with (afold (plus a₁' a₁'') s) in eq-p
 ... | plus v v₁ rewrite eq-p rewrite a₁-idem = refl 
 afold-idem (plus a a₁) s | a-idem | a₁-idem | var id | a₁' 
  with (s id) in eq-sid | (afold a₁' s) in eq-a₁'
 ... | nothing | const n  rewrite a-idem rewrite a₁-idem = refl
 ... | nothing | var id₁  rewrite a-idem rewrite a₁-idem = refl
 ... | nothing | plus v v₁ rewrite a-idem rewrite a₁-idem = refl
 afold-idem (plus a a₁) s | a-idem | a₁-idem | plus a' a'' | a₁' 
  with (afold (plus a' a'') s) in eq-plus | (afold a₁' s) in eq-a₁'
 ... | plus v v₁ | const n rewrite a-idem rewrite a₁-idem = refl
 ... | plus v v₁ | var id rewrite a-idem rewrite a₁-idem = refl
 ... | plus v v₁ | plus v' v'' rewrite a-idem rewrite a₁-idem = refl
 
 -- Folding preserves semantics.
 afold-sound : ∀ a {s t : Store} {p : t ≅ s} -> (aeval a s ≡ aeval (afold a t) s)
 afold-sound = ?
