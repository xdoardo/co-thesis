------------------------------------------------------------------------
-- Properties of Stack compilation of Imp
------------------------------------------------------------------------
module Stack.Imp.Compile.Properties where 

open import Data.Maybe
open import Data.Product
open import Data.Integer
open import Stack.Syntax
open import Imp.Semantics 
open import Imp.Semantics.Properties
open import Stack.Semantics 
open import Stack.Imp.Compile
open import Imp.Syntax hiding (_,_) 
open import Stack.Syntax.Properties
open import Data.Nat renaming (_+_ to _+n_)
open import Data.List renaming (_∷_ to _::_)
open import Codata.Sized.Delay
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
---

open ≡-Reasoning 
---

comp-aexp-correct : ∀ aexp code s pc σ {v} -> (a-wf : aeval-wf s {v} aexp)  -> 
 (c-at : code-at code pc (comp-aexp aexp) ) -> 
  (code , pc , σ , s) =<*> (code , pc +n codelen (comp-aexp aexp) , v :: σ , s)
comp-aexp-correct (const x) code s pc σ (wf-const .x) 
 (at c₁ .(comp-aexp (const x)) c₃ .pc x₁) = 
  continue (code , pc , σ , s) (at c₁ (iconst x :: []) c₃ pc x₁) 
   (code , pc +n 1 , x :: σ , s) refl ◅ ε
comp-aexp-correct (var x) code s pc σ (wf-var .x) (at c₁ .(comp-aexp (var x)) c₃ .pc x₁) = 
  continue (code , pc , σ , s) 
   (at c₁ (comp-aexp (var x)) c₃ pc x₁)
    (code , pc +n 1 , s x :: σ , s) refl  ◅ ε
comp-aexp-correct (plus aexp aexp₁) code s pc σ 
 (wf-plus .aexp .aexp₁ v₁ v₂ a-wf a-wf₁) 
  (at c₁ .(comp-aexp (plus aexp aexp₁)) c₃ .pc x) = 
  let 
   comp-p = (comp-aexp aexp ++ comp-aexp aexp₁ ++ iadd :: [])
   code = c₁ ++ comp-p ++ c₃
   c-aexp = comp-aexp aexp
   c-aexp₁ = comp-aexp aexp₁
   c-at = (at c₁ comp-p c₃ pc x)
   c-at₁ = (code-at-next code 
       (comp-aexp aexp) (comp-aexp aexp₁ ++ iadd :: []) pc c-at)
   c-at₂ = (code-at-next code  
      (comp-aexp aexp₁) (iadd :: []) 
       (pc +n foldr (λ _ → ℕ.suc) zero (comp-aexp aexp)) 
        c-at₁)
  in
   comp-aexp-correct aexp code s pc σ a-wf (code-at-append code (comp-aexp aexp) 
    (comp-aexp aexp₁ ++ iadd :: []) pc c-at) 
  ◅◅ 
    comp-aexp-correct aexp₁ code s (pc +n codelen c-aexp) (v₁ :: σ) a-wf₁ 
    (code-at-append code (comp-aexp aexp₁) (iadd :: []) 
    (pc +n (codelen c-aexp)) c-at₁) ◅◅ {! !} ◅ ε
--  let 
--   clen = codelen (comp-aexp (plus aexp aexp₁)) 
--   comp-p = (comp-aexp aexp ++ comp-aexp aexp₁ ++ iadd :: [])
--   code = c₁ ++ comp-p ++ c₃
--   c-aexp = comp-aexp aexp
--   c-aexp₁ = comp-aexp aexp₁
--   c-at = (at c₁ comp-p c₃ pc x)
--   c-at₁ = (code-at-next code 
--       (comp-aexp aexp) (comp-aexp aexp₁ ++ iadd :: []) pc c-at)
--   c-at₂ = (code-at-next code  
--      (comp-aexp aexp₁) (iadd :: []) 
--       (pc +n foldr (λ _ → ℕ.suc) zero (comp-aexp aexp)) 
--        c-at₁)
--  in 
--    continue (code , pc , σ , s) 
--     c-at (code , pc +n codelen c-aexp , v₁ :: σ , s) refl
--   ◅ 
--    continue (code , pc +n codelen c-aexp , v₁ :: σ , s)
--     c-at₁ (code , pc +n codelen c-aexp +n codelen c-aexp₁ , v₂ :: v₁ :: σ , s) refl
--   ◅ 
--    continue (code , pc +n codelen c-aexp +n codelen c-aexp₁ , v₂ :: v₁ :: σ , s)
--      c-at₂ (code , pc +n clen , v₁ + v₂ :: σ , s) refl
--   ◅ ε
comp-aexp-correct (minus aexp aexp₁) code s pc σ a-wf c-at = {! !}
comp-aexp-correct (times aexp aexp₁) code s pc σ a-wf c-at = {! !}
comp-aexp-correct (div aexp aexp₁) code s pc σ a-wf c-at = {! !}
