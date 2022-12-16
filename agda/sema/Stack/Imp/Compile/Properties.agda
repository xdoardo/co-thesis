------------------------------------------------------------------------
-- Properties of Stack compilation of Imp
------------------------------------------------------------------------
module Stack.Imp.Compile.Properties where 

open import Data.Maybe
open import Data.Product
open import Data.Integer
open import Stack.Syntax
open import Imp.Semantics 
open import Stack.Semantics
open import Stack.Imp.Compile
open import Imp.Syntax hiding (_,_) 
open import Stack.Syntax.Properties
open import Data.Nat renaming (_+_ to _+n_)
open import Data.List renaming (_∷_ to _::_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
---


comp-aexp-correct : ∀ (aexp : AExp) (code : Code) s (pc : PC) (σ : Stack) {v} -> 
                     (c-at : code-at code pc (comp-aexp aexp)) -> (a-wf : aeval-wf s {v} aexp ) ->  
                      (pc , σ , s) =< code > (pc +n codelen (comp-aexp aexp) , v :: σ , s)
comp-aexp-correct (const x) code s pc σ c-at (wf-const .x) = 
 (=>const pc σ s x (code-at=>instr-at c-at)) ◅ ε
comp-aexp-correct (var x) code s pc σ c-at (wf-var .x) =
 (=>var pc σ s x (s x) (code-at=>instr-at c-at) refl) ◅ ε
comp-aexp-correct (plus aexp aexp₁) code s pc σ c-at (wf-plus .aexp .aexp₁ v₁ v₂ a-wf a-wf₁) = 
  (comp-aexp-correct aexp code s pc σ ? a-wf) 
 ◅◅ 
  (comp-aexp-correct aexp₁ code s 
   (pc +n codelen (comp-aexp aexp)) (v₁ :: σ) ? a-wf₁) 
 ◅◅ 
  (=>add 
   (pc +n codelen (comp-aexp aexp) +n codelen (comp-aexp aexp₁)) 
     σ s v₁ v₂ ?)
 ◅ ?
comp-aexp-correct (minus aexp aexp₁) code s pc σ c-at a-wf = {! !}
comp-aexp-correct (times aexp aexp₁) code s pc σ c-at a-wf = {! !}
comp-aexp-correct (div aexp aexp₁) code s pc σ c-at a-wf = {! !}
