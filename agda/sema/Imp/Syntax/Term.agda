------------------------------------------------------------------------
-- Terms for imp 
-----------------------------------------------------------------------
module Imp.Syntax.Term where 

open import Data.Integer as Int using (ℤ)
open import Data.Bool as Bool using (Bool)
open import Data.String as String using (String)
--


infixl 6 _+_ _-_
infixl 7 _*_

-- Arithmetic expressions 
data AExp : Set where 
 lit : (n : ℤ) -> AExp
 var : String -> AExp
 _+_ _-_ _*_ : AExp -> AExp -> AExp

infixl 2 _∧_ _∨_
infix 4 _==_ _≤_ 

infix 2 ¬_

-- Boolean expressions
data BExp : Set where
  lit : Bool -> BExp
  _∧_ _∨_ : BExp -> BExp -> BExp
  _==_  _≤_  : AExp -> AExp -> BExp
  ¬_ : BExp -> BExp


-- Commands
infix 3 _:=_
infixl 2 _>>_
infix 1 if_then_else_
infix 1 while_dO_

data Com : Set where
  skip : Com
  _:=_ : String -> AExp -> Com
  _>>_ : Com -> Com -> Com
  if_then_else_ : BExp -> Com -> Com -> Com
  while_dO_ : BExp -> Com -> Com
