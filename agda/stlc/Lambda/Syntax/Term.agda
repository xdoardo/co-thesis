------------------------------------------------------------------------
-- Terms for the λ-calculus
-----------------------------------------------------------------------
module Lambda.Syntax.Term where

open import Data.Nat
open import Relation.Nullary.Decidable
open import Data.Fin using (Fin ; #_ ; zero ; suc)
---

-- Terms. Variables are represented using de Brujin indices. 
data Tm (n : ℕ) : Set where
  t-con : (i : ℕ) → Tm n
  t-var : (x : Fin n) → Tm n
  t-lam : (t : Tm (suc n)) → Tm n
  t-app : (t₁ t₂ : Tm n) → Tm n

-- Convenient helper.
vr : ∀ m {n} {m<n : True (suc m ≤? n)} → Tm n
vr _ {m<n = m<n} = t-var (#_ _ {m<n = m<n})
