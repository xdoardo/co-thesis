---------------------------------------------------------------------------
-- Terms 
---------------------------------------------------------------------------

module Lambda.Term where 

open import Lambda.Type
open import Lambda.Context

data Tm  (Γ : Ctx) :  (a : Ty) -> Set where 
  var : ∀ {a}   (x : Var Γ a)                    -> Tm Γ a
  abs : ∀ {a b} (t : Tm (Γ , a) b)               -> Tm Γ (a => b)
  app : ∀ {a b} (t : Tm Γ (a => b)) (u : Tm Γ a) -> Tm Γ b

---------------------------------------------------------------------------
-- Neutral terms
---------------------------------------------------------------------------

data Ne (Ξ : Ctx -> Ty -> Set) (Γ : Ctx) : Ty -> Set where 
  var : ∀ {a} -> Var Γ a -> Ne Ξ Γ a
  app : ∀ {a b} -> Ne Ξ Γ (a => b) -> Ξ Γ a -> Ne Ξ Γ b
