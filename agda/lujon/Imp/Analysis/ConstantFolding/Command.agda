------------------------------------------------------------------------
-- Constant folding for commands of Imp
------------------------------------------------------------------------
module Imp.Analysis.ConstantFolding.Command where

open import Imp.Syntax
open import Imp.Analysis.ConstantFolding.Arith
---

private 
 cdefs : (c : Command) -> (s : Store) -> Store
 cdefs skip s = s
 cdefs (assign id a) s with (afold a s) 
 ... | const n = update id n s
 ... | _ = remove id s
 cdefs (seq c c₁) s = {! !}
 cdefs (ifelse b cᵗ cᶠ) s = merge (cdefs cᵗ s) (cdefs cᶠ s)
 cdefs (while b c) s = {! !}

-- Constant folding (and constant propagation) of commands
cfold : (c : Command) -> (s : Store) -> Command
cfold skip s = skip
cfold (assign id a) s = assign id (afold a s) 
cfold (seq c c₁) s = {! !}
cfold (ifelse b c c₁) s = {! !}
cfold (while b c) s = {! !}
