------------------------------------------------------------------------
-- Properties of the semantics of IMP 
------------------------------------------------------------------------
module Imp.Semantics.Properties where 

open import Imp.Syntax
open import Data.Integer
--

data aeval-wf  (s : Store) : {ℤ} -> AExp -> Set where 
 wf-const : ∀ c -> aeval-wf s {c} (const c) 
 wf-var : ∀ id -> aeval-wf s {s id} (var id)
 wf-plus : ∀ a₁ a₂ v₁ v₂ -> aeval-wf s {v₁} a₁ -> aeval-wf s {v₂} a₂ -> 
            aeval-wf s {v₂ + v₁} (plus a₁ a₂)
 wf-minus : ∀ a₁ a₂ v₁ v₂ -> aeval-wf s {v₁} a₁ -> aeval-wf s {v₂} a₂ -> 
            aeval-wf s {v₁ - v₂} (minus a₁ a₂)
 wf-times : ∀ a₁ a₂ v₁ v₂ -> aeval-wf s {v₁} a₁ -> aeval-wf s {v₂} a₂ -> 
            aeval-wf s {v₁ * v₂} (times a₁ a₂)
 wf-div : ∀ a₁ a₂ v₁ v₂ -> aeval-wf s {v₁} a₁ -> aeval-wf s {v₂} a₂ -> 
           (nz : NonZero v₂) -> aeval-wf s {_/_ v₁ v₂ {{nz}}} (div a₁ a₂)
