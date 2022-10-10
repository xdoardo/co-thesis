{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Size

-- T i ≈ Set with a fake size dependency.
-- We have   Set → T i  but  T i → Set  is only facilitated by the Embed trick.

record T i : Set₁ where
  coinductive
  field force : (j : Size< i) → Set
open T

-- Embed ∞ A ≅ A .force ∞  for  A : T ∞

data Embed : ∀ i → T i → Set where
  abs : {A : T ∞} → A .force ∞ → Embed ∞ A

app : {A : T ∞} → Embed ∞ A → A .force ∞
app (abs x) = x

-- Because Embed is given the more general type  (i : Size) (A : T i) → Set,
-- we get j : Size< i from the invocation  Embed i λ{ .force j → ?}  where ? : Set.
-- This gives a fixed-point combinator on Set.

Fix′ : Size → (Set → Set) → Set
Fix′ i F = F (Embed i λ{ .force j → Fix′ j F})

-- Now we can replay the Russel paradox:

data ⊥ : Set where

Omega : Set
Omega = Fix′ ∞ (λ A → A → ⊥)

self : Omega
self x = app x x

loop : ⊥
loop = self (abs self)
