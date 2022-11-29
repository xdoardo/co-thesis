------------------------------------------------------------------------
-- Equality for terms of the λ-calculus
-----------------------------------------------------------------------
module Lambda.Syntax.Term.Equality where 

open import Lambda.Syntax.Term.Core
open import Relation.Binary
--

data _≡ₜ_ {n} : Tm n -> Tm n -> Set where 
  t-con : ∀ {i} -> t-con i ≡ₜ t-con i
  t-var : ∀ {x} -> t-var x ≡ₜ t-var x
  t-lam : ∀ {t₁ t₂} -> t₁ ≡ₜ t₂ -> t-lam t₁ ≡ₜ t-lam t₂
  t-app : ∀ {t₁ t₂ t₃ t₄} -> t₁ ≡ₜ t₃ -> t₂ ≡ₜ t₄ -> t-app t₁ t₂ ≡ₜ t-app t₃ t₄

module Equivalence where 

 reflexive : ∀ {n} -> Reflexive (_≡ₜ_ {n})
 reflexive {n} {t-con i} = t-con
 reflexive {n} {t-var x} = t-var
 reflexive {n} {t-lam x} = t-lam reflexive
 reflexive {n} {t-app x x₁} = t-app reflexive reflexive
 
 symmetric : ∀ {n} -> Sym (_≡ₜ_ {n}) (_≡ₜ_ {n})
 symmetric t-con = t-con
 symmetric t-var = t-var
 symmetric (t-lam r) = t-lam (symmetric r)
 symmetric (t-app r r₁) = t-app (symmetric r) (symmetric r₁)
 
 transitive : ∀ {n} -> Trans (_≡ₜ_ {n}) (_≡ₜ_ {n}) (_≡ₜ_ {n})
 transitive t-con t-con = t-con
 transitive t-var t-var = t-var
 transitive (t-lam x) (t-lam x₁) = t-lam (transitive x x₁)
 transitive (t-app x x₂) (t-app x₁ x₃) = t-app (transitive x x₁) (transitive x₂ x₃)

open Equivalence public
