------------------------------------------------------------------------
-- Constant folding and propagation for IMP and its properties
------------------------------------------------------------------------
module Imp.Analysis.ConstantFolding where 

open import Imp.Syntax 
open import Data.Product
open import Data.Integer using (ℤ ; _+_ )
--


private 
 fold-bexp : (b : BExp) -> (s : Store) -> BExp
 fold-bexp = ? 
