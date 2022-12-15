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

-- compile-aexp-correct : ∀ a c c₂ pc s σ  -> 
--    (c₂≡comp-aexp : c₂ ≡ (comp-aexp a)) -> 
--    (code-at : code-at c pc (comp-aexp a)) -> (a≡v : aeval a s ≡ just v) -> 
--     Transitions c (pc , σ , s) (pc +n codelen (comp-aexp a) , v :: σ , s)
-- compile-aexp-correct (const x) c (iconst n :: c₂) pc s .x σ c₂≡comp-aexp code-at₁ refl = 
--  (=>const pc σ s x (code-at=>instr-at code-at₁)) ◅ ε
-- compile-aexp-correct (var x) c (ivar id :: c₂) pc s v σ c₂≡comp-aexp code-at₁ a≡v = 
--  (=>var pc σ s x v (code-at=>instr-at code-at₁) a≡v) ◅ ε
-- compile-aexp-correct (plus a a₁) c c₂ pc s v σ c₂≡comp-aexp code-at₁ a≡v = let 
--   a-comp = compile-aexp-correct a c (comp-aexp a) pc s v σ refl ? ? 
--   a₁-comp = compile-aexp-correct a₁ c (comp-aexp a) pc s ? σ ? ? ? 
--  in ?
-- compile-aexp-correct (minus a a₁) c c₂ pc s v σ c₂≡comp-aexp code-at₁ a≡v = {! !}
-- compile-aexp-correct (times a a₁) c c₂ pc s v σ c₂≡comp-aexp code-at₁ a≡v = {! !}
-- compile-aexp-correct (div a a₁) c c₂ pc s v σ c₂≡comp-aexp code-at₁ a≡v = {! !}
