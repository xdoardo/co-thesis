------------------------------------------------------------------------
-- Functional small step semantics for Stack
------------------------------------------------------------------------

module Stack.Semantics.Functional where 

open import Data.Unit
open import Data.Bool 
open import Data.Maybe
open import Data.Integer
open import Data.Product
open import Stack.Syntax
open import Codata.Sized.Delay
open import Codata.Sized.Thunk
open import Stack.Syntax.Properties
open import Data.List renaming (_∷_ to _::_)
open import Relation.Binary.PropositionalEquality
open import Data.Integer.Properties as ℤ-Properties
open import Data.Nat using (ℕ) renaming (_+_ to _+n_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
---

private 
 isNonZero : ∀ (n : ℤ) -> Maybe (NonZero n)
 isNonZero (+_ Data.Nat.zero) = nothing
 isNonZero +[1+ n ] = just (record { nonZero = tt })
 isNonZero (-[1+_] n) = just (record { nonZero = tt }) 

 isNat : ∀ (n : ℤ) -> Maybe (ℕ)
 isNat (+_ n) = just n 
 isNat (-[1+_] n) = nothing
 
 _==ᵇ_ : ∀ (n₁ n₂ : ℤ) -> Bool 
 n₁ ==ᵇ n₂ = if ((n₁ ≤ᵇ n₂) ∧ (n₂ ≤ᵇ n₁)) then true else false

-- The result of running the VM one step.

data Result : Set where
  continue : (s : State) → Result
  done     : (s : State) → Result
  crash    : Result

step : ∀ {c} ((code , pc , σ , ρ) : State) -> code-at code pc c -> Result 
step (code , pc , σ , ρ) (at c₁ [] c₃ .pc x) = done (code , pc , σ , ρ) 
step (code , pc , σ , ρ) (at c₁ (iconst n :: c₂) c₃ .pc x) = 
 continue (code , pc +n 1 , n :: σ , ρ)
step (code , pc , σ , ρ) (at c₁ (ivar id :: c₂) c₃ .pc x) = 
 continue (code , pc +n 1 , (ρ id) :: σ , ρ)
step (code , pc , n :: σ , ρ) (at c₁ (isetvar id :: c₂) c₃ .pc x) =
 continue (code , pc +n 1 , σ , (update id n ρ)) 
step (code , pc , n₁ :: n₂ :: σ , ρ) (at c₁ (imul :: c₂) c₃ .pc x) = 
 continue (code , pc +n 1 , (n₁ * n₂) :: σ , ρ)
step (code , pc , n₁ :: n₂ :: σ , ρ) (at c₁ (idiv :: c₂) c₃ .pc x) with isNonZero n₂
...  | just n = continue (code , pc +n 1 , (_/_  n₁ n₂ {{n}}) :: σ , ρ)
...  | nothing = crash 
step (code , pc , n₁ :: n₂ :: σ , ρ) (at c₁ (iadd :: c₂) c₃ .pc x) = 
 continue (code , pc +n 1 , (n₁ + n₂) :: σ , ρ)
step (code , pc , n :: σ , ρ) (at c₁ (iopp :: c₂) c₃ .pc x) = 
 continue (code , pc +n 1 , (- n) :: σ , ρ)
step (code , pc , σ , ρ) (at c₁ (ibranch d :: c₂) c₃ .pc x) with isNat ((+ pc) + d)
...  | just pc₁ = continue (code , pc₁ , σ , ρ)
...  | nothing = crash
step (code , pc , n₁ :: n₂ :: σ , ρ) (at c₁ (ibeq d₁ d₀ :: c₂) c₃ .pc x) 
 with isNat ((+ pc) + d₁) | isNat ((+ pc) + d₀)
...  | just pc₁ | just pc₂ = 
      if n₁ ==ᵇ n₂ then 
       continue (code , pc₁ , σ , ρ)
      else
       continue (code , pc₂ , σ , ρ)
...  | nothing | just pc₂ = if n₁ ==ᵇ n₂ then crash else continue (code , pc₂ , σ , ρ)
...  | just pc₁ | nothing = if n₁ ==ᵇ n₂ then continue (code , pc₁ , σ , ρ) else crash
...  | nothing | nothing = crash 
step (code , pc , n₁ :: n₂ :: σ , ρ) (at c₁ (ibleq d₁ d₀ :: c₂) c₃ .pc x) 
 with isNat ((+ pc) + d₁) | isNat ((+ pc) + d₀)
...  | just pc₁ | just pc₂ = 
      if n₁ ≤ᵇ n₂ then 
       continue (code , pc₁ , σ , ρ)
      else
       continue (code , pc₂ , σ , ρ)
...  | nothing | just pc₂ = if n₁ ≤ᵇ n₂ then crash else continue (code , pc₂ , σ , ρ)
...  | just pc₁ | nothing = if n₁ ≤ᵇ n₂ then continue (code , pc₁ , σ , ρ) else crash
...  | nothing | nothing = crash 
step (code , pc , σ , ρ) (at c₁ (ihalt :: c₂) c₃ .pc x) =
 done (code , pc , σ , ρ)
step _ _  = crash


data _=<>_ : State ->  State -> Set where
 continue : ∀  {c}  ((code , pc , σ , ρ) : State) (c-at : code-at code pc c) -> (s : State) ->
  step (code , pc , σ , ρ) c-at ≡ continue s -> (code , pc , σ , ρ) =<> s
 done : ∀  {c} ((code , pc , σ , ρ) : State) (c-at : code-at code pc c) -> (s : State) -> 
  step (code , pc , σ , ρ) c-at ≡ done s -> (code , pc , σ , ρ) =<> s

_=<*>_ : State -> State -> Set 
_=<*>_ = Star _=<>_
