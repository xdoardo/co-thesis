------------------------------------------------------------------------
-- Definite initialization for arithmetic expressions of Imp
------------------------------------------------------------------------
module Imp.Analysis.DefiniteInitialization.Arith where

open import Data.Maybe 
open import Data.Bool
open import Imp.Syntax renaming (_,_ to _,ₛ_)
open AExp
---

dia-aexp : AExp -> Store -> Maybe Store
dia-aexp (const x) s = just s 
dia-aexp (var x) s with (s x) 
... | nothing = nothing 
... | just v = just s
dia-aexp (plus x x₁) t = dia-aexp x t >>= λ _ -> dia-aexp x₁ t >>= λ _ -> just t


------------------------------------------------------------------------
-- Properties of definite initialization for arithmetic expressions
------------------------------------------------------------------------
module _ where 
 open import Data.List
 open import Data.Product 
 open import Data.Integer 
 open import Relation.Nullary.Decidable
 open import Data.List.Relation.Unary.Any
 open import Imp.Semantics.Functional.Arith
 open import Relation.Binary.PropositionalEquality
 --- 

 --- 
 private 
  lem : ∀ id -> ∃ λ v -> vars-aexp (var id) id ≡ just v 
  lem id rewrite (==-refl {id}) = 0ℤ , refl 

 -- For every arithmetic expression a and store s, if the set of variables 
 a⊆s-aeval-some : ∀ (a : AExp) (s : Store) -> (a⊆s : (vars-aexp a) ⊆ᵤ s) -> ∃ λ v' -> aeval a s ≡ just v'
 a⊆s-aeval-some (const n) s a⊆s = n , refl
 a⊆s-aeval-some (var id) s a⊆s = a⊆s id (lem id)
 a⊆s-aeval-some (plus a a₁) s a⊆s with (a⊆s-aeval-some a s 
     (trans-⊆ᵤ (vars-aexp a) (vars-aexp (plus a a₁)) s (⊆ᵃ-⊆ᵤ a (plus a a₁) (plus-l a a₁)) a⊆s)) 
  | (a⊆s-aeval-some a₁ s 
     (trans-⊆ᵤ (vars-aexp a₁) (vars-aexp (plus a a₁)) s  (⊆ᵃ-⊆ᵤ a₁ (plus a a₁) (plus-r a a₁)) a⊆s))
 ... | v , v-eq | v₁ , v₁-eq rewrite v-eq rewrite v₁-eq = (v + v₁) , refl 


-- -- For every arithmetic expression a and store s, if evaluating a in s results
-- -- in nothing then the definite initialization of a in s results in nothing as
-- -- well. 
-- dia-aexp-nothing : ∀ (a : AExp) (s : Store) -> (aeval-nothing : aeval a s ≡ nothing) -> dia-aexp a s ≡ nothing
-- dia-aexp-nothing (var id) s aeval-nothing with (s id)
-- ... | nothing = refl
-- dia-aexp-nothing (plus a a₁) s aeval-nothing with (aeval a s) in aeval-a | (aeval a₁ s) in aeval-a₁
-- ... | just x | nothing with (dia-aexp a s)
-- ... | just x₁ rewrite (dia-aexp-nothing a₁ s aeval-a₁) = refl
-- ... | nothing = refl
-- dia-aexp-nothing (plus a a₁) s aeval-nothing | nothing | nothing rewrite (dia-aexp-nothing a s aeval-a) = refl 
-- dia-aexp-nothing (plus a a₁) s aeval-nothing | nothing | _ rewrite (dia-aexp-nothing a s aeval-a) = refl
--
--
-- -- For every arithmetic expression a and store s, if the definite
-- -- initialization analysis results in something different from nothing (i.e.
-- -- just s'), then the evaluation of a in s results in something different from
-- -- nothing (i.e. just v).
-- aeval-some : ∀ (a : AExp) (s : Store) -> (dia-some : dia-aexp a s ≢ nothing) -> aeval a s ≢ nothing
-- aeval-some (var id) s dia-some aeval-some with (s id)
-- ... | nothing = dia-some refl 
-- aeval-some (plus a a₁) s dia-some aeval-some = dia-some (dia-aexp-nothing (plus a a₁) s aeval-some)
