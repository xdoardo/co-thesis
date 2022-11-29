------------------------------------------------------------------------
-- Equality for values of the λ-calculus
-----------------------------------------------------------------------
module Lambda.Syntax.Value.Equality where

open import Data.Nat
open import Relation.Binary
open import Lambda.Syntax.Term.Core 
open import Lambda.Syntax.Value.Core
open import Lambda.Syntax.Term.Equality renaming (reflexive to t-refl ; symmetric to t-sym ; transitive to t-trans)
open import Relation.Binary.PropositionalEquality using (_≡_ ; sym ; trans)
--

data _≡ᵥ_ : Value -> Value -> Set where
  v-con : ∀ {i} -> v-con i ≡ᵥ v-con i
  v-lam : ∀ {n} {t₁ t₂ : Tm (suc n)} {ρ₁ ρ₂ : Env n} -> t₁ ≡ₜ t₂ -> ρ₁ ≡ ρ₂ -> 
           v-lam t₁ ρ₁ ≡ᵥ v-lam t₂ ρ₂

module Equality where
  
  -- This is an equivalence 
  reflexive : Reflexive (_≡ᵥ_)
  reflexive {v-con i} = v-con
  reflexive {v-lam t ρ} = v-lam (t-refl) _≡_.refl 
  
  
  symmetric : Sym (_≡ᵥ_) (_≡ᵥ_)
  symmetric v-con = v-con
  symmetric (v-lam x x₁) = v-lam (t-sym x) (sym x₁)
  
  transitive : Trans (_≡ᵥ_) (_≡ᵥ_) (_≡ᵥ_)
  transitive v-con v-con = v-con
  transitive (v-lam x x₂) (v-lam x₁ x₃) = v-lam (t-trans x x₁) (trans x₂ x₃)
  
open Equality public
