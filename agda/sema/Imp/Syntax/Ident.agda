------------------------------------------------------------------------
-- Identifiers of IMP
------------------------------------------------------------------------
module Imp.Syntax.Ident where 

open import Data.Bool
open import Data.Maybe
open import Data.String
open import Data.Integer using (ℤ)
---

Ident : Set 
Ident = String

Store : Set
Store = Ident -> Maybe ℤ 

empty : Store 
empty = λ _ -> nothing

update : (i : Ident) -> (v : ℤ) -> (s : Store) -> Store 
update i v s = λ x -> if x == i then just (v) else (s x)
