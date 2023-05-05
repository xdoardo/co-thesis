------------------------------------------------------------------------
-- Identifiers of Imp
------------------------------------------------------------------------
module Imp.Syntax.Ident where 

open import Data.Bool
open import Data.Maybe
open import Data.String
open import Data.Integer using (ℤ ; 0ℤ)
---

Ident : Set 
Ident = String

Store : Set
Store = Ident -> ℤ 

empty : Store 
empty = λ _ -> 0ℤ 

update : (i : Ident) -> (v : ℤ) -> (s : Store) -> Store 
update i v s = λ x -> if x == i then v else (s x)
