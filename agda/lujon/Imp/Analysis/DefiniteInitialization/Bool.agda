------------------------------------------------------------------------
-- Definite initialization for boolean expressions of Imp
------------------------------------------------------------------------
module Imp.Analysis.DefiniteInitialization.Bool where

open import Data.Maybe 
open import Imp.Syntax renaming (_,_ to _,ₛ_)
open import Data.Bool renaming (not to bnot)
open import Imp.Analysis.DefiniteInitialization.Arith
---

open BExp
---

dia-bexp : (b : BExp) -> (s : Store) -> Maybe Store
dia-bexp (const b) s = just s
dia-bexp (le a₁ a₂) s = dia-aexp a₁ s >>= λ _ -> dia-aexp a₂ s >>= λ _ -> just s
dia-bexp (not b) s = dia-bexp b s
dia-bexp (and b₁ b₂) s = dia-bexp b₁ s >>= λ _ -> dia-bexp b₂ s >>= λ _ -> just s 

------------------------------------------------------------------------
-- Properties of definite initialization for boolean expressions
------------------------------------------------------------------------
module _ where 
 open import Data.Product 
 open import Data.Integer
 open import Imp.Semantics.Functional.Bool
 open import Imp.Semantics.Functional.Arith
 open import Relation.Binary.PropositionalEquality
 open import Imp.Analysis.DefiniteInitialization.Arith
 ---

 
 b⊆s-beval-some : ∀ (b : BExp) (s : Store) -> (b⊆s : (vars-bexp b) ⊆ᵤ s) -> ∃ λ v' -> beval b s ≡ just v'
 b⊆s-beval-some (const b) s b⊆s = b , refl
 b⊆s-beval-some (le a₁ a₂) s b⊆s 
  with 
   (a⊆s-aeval-some a₁ s 
     (trans-⊆ᵤ (vars-aexp a₁) (vars-bexp (le a₁ a₂)) s (⊆ᵃᵇ-⊆ᵤ a₁ (le a₁ a₂) (le-l a₁ a₂)) b⊆s)) 
  | 
   (a⊆s-aeval-some a₂ s 
    (trans-⊆ᵤ (vars-aexp a₂) (vars-bexp (le a₁ a₂)) s (⊆ᵃᵇ-⊆ᵤ a₂ (le a₁ a₂) (le-r a₁ a₂)) b⊆s))
 ... | v , v-eq | v' , v'-eq rewrite v-eq rewrite v'-eq = (v ≤ᵇ v') , refl
 b⊆s-beval-some (not b) s b⊆s with 
  (b⊆s-beval-some b s (trans-⊆ᵤ (vars-bexp b) (vars-bexp (not b)) s (⊆ᵇ-⊆ᵤ b (not b) (not b)) b⊆s)) 
 ... | v , v-eq rewrite v-eq = bnot v , refl
 b⊆s-beval-some (and b b₁) s b⊆s 
  with 
   (b⊆s-beval-some b s (trans-⊆ᵤ (vars-bexp b) (vars-bexp (and b b₁)) s (⊆ᵇ-⊆ᵤ b (and b b₁) (and-l b b₁)) b⊆s)) 
  | 
   (b⊆s-beval-some b₁ s (trans-⊆ᵤ (vars-bexp b₁) (vars-bexp (and b b₁)) s (⊆ᵇ-⊆ᵤ b₁ (and b b₁) (and-r b b₁)) b⊆s)) 
 ... | v , v-eq | v' , v'-eq rewrite v-eq rewrite v'-eq = (v ∧ v') , refl 

-- -- For every boolean expression b and store s, if evaluating b in s results
-- -- in nothing then the definite initialization of b in s results in nothing as
-- -- well. 
-- dia-bexp-nothing : ∀ (b : BExp) (s : Store) -> (eval-nothing : beval b s ≡ nothing) -> dia-bexp b s ≡ nothing
-- dia-bexp-nothing (le a₁ a₂) s eval-nothing with (aeval a₁ s) in eq-a₁ | (aeval a₂ s) in eq-a₂
-- ... | just x | nothing rewrite (dia-aexp-nothing a₂ s eq-a₂) with (dia-aexp a₁ s) in eq-dia-a₁
-- ... | just x₁ = refl
-- ... | nothing = refl
-- dia-bexp-nothing (le a₁ a₂) s eval-nothing | nothing | just x rewrite (dia-aexp-nothing a₁ s eq-a₁) = refl
-- dia-bexp-nothing (le a₁ a₂) s eval-nothing | nothing | nothing rewrite (dia-aexp-nothing a₁ s eq-a₁) = refl
-- dia-bexp-nothing (not b) s eval-nothing with (beval b s) in eq-b
-- ... | nothing = dia-bexp-nothing b s eq-b
-- dia-bexp-nothing (and b₁ b₂) s eval-nothing with (beval b₁ s) in eq-b₁ | (beval b₂ s) in eq-b₂
-- ... | just x | nothing rewrite (dia-bexp-nothing b₂ s eq-b₂) with (dia-bexp b₁ s) in eq-dia-b₁
-- ... | just x₁ = refl
-- ... | nothing = refl
-- dia-bexp-nothing (and b₁ b₂) s eval-nothing | nothing | just x rewrite (dia-bexp-nothing b₁ s eq-b₁) = refl
-- dia-bexp-nothing (and b₁ b₂) s eval-nothing | nothing | nothing rewrite (dia-bexp-nothing b₁ s eq-b₁) = refl
--
--
-- -- For every boolean expression b and store s, if the definite
-- -- initialization analysis results in something different from nothing (i.e.
-- -- just s'), then the evaluation of b in s results in something different from
-- -- nothing (i.e. just v).
-- beval-some : ∀ (b : BExp) (s : Store) -> (dia-some : dia-bexp b s ≢ nothing) -> beval b s ≢ nothing
-- beval-some (const b) s dia-some eval-some rewrite (dia-bexp-nothing (const b) s eval-some) = dia-some refl
-- beval-some (le a₁ a₂) s dia-some eval-some = dia-some (dia-bexp-nothing (le a₁ a₂) s eval-some)
-- beval-some (not b) s dia-some eval-some = dia-some (dia-bexp-nothing (not b) s eval-some)
-- beval-some (and b b₁) s dia-some eval-some = dia-some (dia-bexp-nothing (and b b₁) s eval-some) 
