------------------------------------------------------------------------
-- Free variables of terms of Imp
------------------------------------------------------------------------
module Imp.Syntax.Vars where 

open import Data.Bool
open import Data.Maybe
open import Imp.Syntax.Core
open import Imp.Syntax.Ident
open import Data.String using (_==_ ; String)
open import Data.IndicatorFunction (String) (_==_) renaming (IndicatorFunction to VarsSet) public
---

avars : (a : AExp) -> VarsSet
avars (const n) = ∅ 
avars (var id) = id ↦ ∅
avars (plus a₁ a₂) = (avars a₁) ∪ (avars a₂)

bvars : (b : BExp) -> VarsSet
bvars (const b) = ∅
bvars (le a₁ a₂) = (avars a₁) ∪ (avars a₂)
bvars (not b) = bvars b 
bvars (and b b₁) = (bvars b) ∪ (bvars b₁)

cvars : (c : Command) -> VarsSet
cvars skip = ∅
cvars (assign id a) = avars a
cvars (seq c c₁) = (cvars c) ∪ (cvars c₁)
cvars (ifelse b c c₁) = ((bvars b) ∪ (cvars c)) ∪ (cvars c₁)
cvars (while b c) = (bvars b) ∪ (cvars c)

-- A function to build a VarsSet from a Store. 
dom : Store -> VarsSet
dom s x with (s x) 
... | just _ = true 
... | nothing = false 
