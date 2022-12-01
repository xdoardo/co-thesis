------------------------------------------------------------------------
-- The syntax of the Imp language 
-----------------------------------------------------------------------
module Imp.Syntax where

open import Imp.Syntax.Term public
open import Imp.Syntax.Value public

------------------------------------------------------------------------
-- Examples 
module _ where 
 open import Data.Bool as Bool 

 -- A non terminating command 
 Ω : Com
 Ω = while (lit Bool.true) dO skip
