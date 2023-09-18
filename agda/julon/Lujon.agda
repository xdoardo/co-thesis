module Lujon where 


-- [misc]: Data 
open import Data.And 
open import Data.Or
open import Data.CharacteristicFunction 

-- Part 1: Weak bisimilarity
open import Codata.Sized.Delay.WeakBisimilarity
open import Codata.Sized.Delay.WeakBisimilarity.Relation.Binary.Equivalence

-- Part 2: Trivial combinators for Delay + Maybe
open import Codata.Sized.FailingDelay.Effectful
open import Codata.Sized.FailingDelay.Relation.Binary.Convergence

-- Part 3: Imp
open import Imp.Syntax
open import Imp.Semantics.BigStep.Functional
open import Imp.Semantics.BigStep.Functional.Properties
open import Imp.Analysis.DefiniteInitialization
-- open import Imp.Analysis.PureFolding
