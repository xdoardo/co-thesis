------------------------------------------------------------------------
-- Constant folding and propagation for IMP and its properties
------------------------------------------------------------------------
module Imp.Analysis.ConstantFolding where 

import Data.Bool as Bool 
open import Data.Unit
open import Imp.Syntax 
open import Data.Maybe
open import Data.Integer 
open import Data.Product renaming (_,_ to _,,_)  
open import Data.Integer.Properties as ℤ-Properties
open import Data.Nat using () renaming (suc to ℕ-suc)
open import Relation.Binary.PropositionalEquality
--


private 
 isNonZero : ∀ (n : ℤ) -> Maybe (NonZero n)
 isNonZero (ℤ.pos (ℕ-suc n)) = just (record { nonZero = tt}) 
 isNonZero (ℤ.negsuc (ℕ-suc n)) = just (record { nonZero = tt}) 
 isNonZero _ = nothing 

 case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
 case x of f = f x
 
 _==ᵇ_ : ℤ -> ℤ -> Bool.Bool
 x ==ᵇ x₁ = Bool.if (x ≤ᵇ x₁) then (Bool.if (x₁ ≤ᵇ x) then Bool.true else Bool.false) else Bool.false

 fold-aexp : (a : AExp) -> (s : Store) -> AExp
 fold-aexp (const x) s = const x 
 fold-aexp (var x) s with (s x)
 ... | just v = const v
 ... | nothing = var x
 fold-aexp (plus a a₁) s with (fold-aexp a s) | (fold-aexp a₁ s)
 ... | const v | const v₁ = const (v + v₁)
 ... | a' | a₁' = plus a' a₁'
 fold-aexp (minus a a₁) s with (fold-aexp a s) | (fold-aexp a₁ s)
 ... | const v | const v₁ = const (v - v₁)
 ... | a' | a₁' = plus a' a₁'
 fold-aexp (times a a₁) s with (fold-aexp a s) | (fold-aexp a₁ s)
 ... | const v | const v₁ = const (v * v₁)
 ... | a' | a₁' = plus a' a₁'
 fold-aexp (div a a₁) s with (fold-aexp a s) | (fold-aexp a₁ s)
 ... | const v | const v₁ = case (isNonZero v₁) of λ { 
  (just t) -> const (_/_ v v₁ {{t}}) ; 
  nothing -> (div a a₁) }
 ... | a' | a₁' = plus a' a₁'

 fold-bexp : (b : BExp) -> (s : Store) -> BExp
 fold-bexp true s = true 
 fold-bexp false s = false 
 fold-bexp (eq a₁ a₂) s with (fold-aexp a₁ s) | (fold-aexp a₂ s)
 ... | const v₁ | const v₂ = Bool.if (v₁ ==ᵇ v₂) then true else false
 ... | a₁ | a₂ = (eq a₁ a₂)
 fold-bexp (leq a₁ a₂) s with (fold-aexp a₁ s) | (fold-aexp a₂ s)
 ... | const v₁ | const v₂ = Bool.if (v₁ ≤ᵇ v₂) then true else false
 ... | a₁ | a₂ = (eq a₁ a₂)
 fold-bexp (not b) s with (fold-bexp b s) 
 ... | true = false 
 ... | false = true 
 ... | b' = (not b')
 fold-bexp (and b b₁) s with  (fold-bexp b s) | (fold-bexp b₁ s)
 ... | true | true = true 
 ... | _ | false = false
 ... | false | _ = false
 ... | b' | b₁' = (and b' b₁')

fold : (c : Command) -> (s : Store) -> (Store × Command)
fold skip s = s ,, skip 
fold (assign id a) s with (fold-aexp a s)
... | const x = (update id x s) ,, skip
... | a' = s ,, (assign id a)
fold (seq c c₁) s = let (s' ,, c') = fold c s in 
 (let (s'' ,, c₁') = fold c₁ s' 
  in (s'' ,, (c' , c₁')))
fold (ifelse b c c₁) s with (fold-bexp b s) | (fold c s) | (fold c₁ s) 
... | true | s' ,, c' | _ = s' ,, c' 
... | false | _ | s' ,, c'  = s' ,, c' 
... | b' | s' ,, c' | s₁' ,, c₁' = (merge s' s₁') ,, (ifelse b' c' c₁')
fold (while b c) s = {! !}
