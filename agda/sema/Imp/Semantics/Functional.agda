------------------------------------------------------------------------
-- Functional semantics for the λ-calculus with constants
------------------------------------------------------------------------
module Imp.Semantics.Functional where 

open import Size 
open import Imp.Syntax
open import Data.Product
open import Codata.Sized.Thunk
open import Codata.Sized.Delay hiding (never)
open import Data.Integer as Int using (ℤ)
open import Data.Bool as Bool using (Bool) 
open import Data.Maybe renaming (_>>=_ to _>>=m_)
open import Codata.Sized.Partial renaming (bind to _>>=_)
--

mutual 
 private
  acomb : AExp -> AExp -> State -> (ℤ -> ℤ -> ℤ) -> Maybe ℤ
  acomb x x₁ ρ f = (aeval x ρ) >>=m λ v₁ -> (aeval x₁ ρ) >>=m λ v₂ -> just (f v₁ v₂)

  bzcomb : AExp -> AExp -> State -> (ℤ -> ℤ -> Bool) -> Maybe Bool
  bzcomb x x₁ ρ f = (aeval x ρ) >>=m λ v₁ -> (aeval x₁ ρ) >>=m λ v₂ -> just (f v₁ v₂)

  bbcomb : BExp -> BExp -> State -> (Bool -> Bool -> Bool) -> Maybe Bool
  bbcomb x x₁ ρ f = (beval x ρ) >>=m λ v₁ -> (beval x₁ ρ) >>=m λ v₂ -> just (f v₁ v₂)

  unpack : Maybe Bool -> Bool
  unpack (just Bool.true) = Bool.true
  unpack _ = Bool.false

 aeval : AExp -> State -> Maybe ℤ
 aeval (lit n) ρ = just n
 aeval (var x) ρ = lookup ρ x
 aeval (x + x₁) ρ = acomb x x₁ ρ Int._+_
 aeval (x - x₁) ρ = acomb x x₁ ρ Int._-_
 aeval (x * x₁) ρ = acomb x x₁ ρ Int._*_

 beval : BExp -> State -> Maybe Bool
 beval (lit x) ρ = just x
 beval (x ∧ x₁) ρ = bbcomb x x₁ ρ  Bool._∧_
 beval (x ∨ x₁) ρ = bbcomb x x₁ ρ  Bool._∨_
 beval (x == x₁) ρ = bzcomb x x₁ ρ λ x y → (x Int.≤ᵇ y) Bool.∧ (y Int.≤ᵇ x)
 beval (x ≤ x₁) ρ = bzcomb x x₁ ρ Int._≤ᵇ_
 beval (¬ x) ρ = beval x ρ >>=m λ v -> just (Bool.not v)

 ceval : ∀ {i} -> Com -> State -> Delay (Maybe Value) i
 ceval skip ρ = now (just (v-empty ρ)) 
 ceval (x := x₁) ρ = now ((aeval x₁ ρ) >>=m λ v -> just (v-empty [ x => v :: ρ ]))
 ceval (x >> x₁) ρ = ceval x ρ >>= λ v -> ceval x₁ ((get-state v) :: ρ)
 ceval (if x then x₁ else x₂) ρ = let b = beval x ρ
  in Bool.if (unpack b) then ceval x₁ ρ else ceval x₂ ρ
 ceval (while x dO x₁) ρ = let b = beval x ρ
  in Bool.if (unpack b) then later (weval x x₁ ρ) else now (just (v-empty ρ))

 weval : ∀ {i} -> BExp -> Com -> State -> Thunk (Delay (Maybe Value)) i
 force (weval x x₁ ρ) = ceval x₁ ρ >>= λ v -> (ceval (while x dO x₁) ((get-state v) :: ρ))

------------------------------------------------------------------------
-- Examples
module _ where 
 open import Codata.Sized.Partial using (never)
 open import Codata.Sized.Partial.Bisimilarity.Weak

 -- Ω is weakly bisimilar to never.
 Ω-loops : ∀ {i} -> i ⊢ (ceval Ω []) ≈ never
 Ω-loops = later (λ where .force -> Ω-loops) 
