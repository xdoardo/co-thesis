---------------------------------------------------------------------------
-- Contexts and variables
---------------------------------------------------------------------------

module Lambda.Context where 

open import Lambda.Type

data Ctx : Set where 
  ε : Ctx 
  _,_ : (Γ : Ctx) (a : Ty) -> Ctx

data Var : (Γ : Ctx) (a : Ty) -> Set where
  zero : ∀ {Γ a} -> Var (Γ , a) a
  suc : ∀ {Γ a b} -> (x : Var Γ a) -> Var (Γ , b) a
