{-# OPTIONS --allow-unsolved-metas #-} 
------------------------------------------------------------------------
-- Properties of functional semantics for Imp
------------------------------------------------------------------------
module Imp.Semantics.BigStep.Functional.Properties where 

open import Size
open import Data.Or
open import Function using (case_of_)
open import Data.Bool
open import Data.Maybe
open import Data.Empty
open import Imp.Syntax
open import Data.Product
open import Data.Integer
open import Data.Irrelevant
open import Codata.Sized.Thunk
open import Data.Bool.Properties
open import Codata.Sized.Delay hiding (_⇓)
open import Imp.Semantics.BigStep.Functional
open import Codata.Sized.Delay.WeakBisimilarity
open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Codata.Sized.FailingDelay.Effectful using () renaming (bind to _>>=ᵖ_)
open import Codata.Sized.FailingDelay.Relation.Binary.Convergence 
open import Data.String using (String ; _==_) renaming (_≟_ to _≟ₛ_)
open import Codata.Sized.Delay.WeakBisimilarity.Relation.Binary.Equivalence using (≡=>≋)
--

⇓=>≡ : ∀ {a} {A : Set a} (x : Delay (Maybe A) ∞) (y z : A) (h : x ⇓ z) (h₁ : x ≡ (now (just y))) -> (z ≡ y)
⇓=>≡ .(now (just y)) y .y (now refl) refl = refl 

mutual 
 private
  while-∻-later :  ∀ {x : Thunk (Delay (Maybe Store)) ∞} (c : Command) (b : BExp) (s s' : Store)  
   (f : ∀ (sⁱ : Store) -> later x ⇓ sⁱ -> s ∻ sⁱ) (h⇓ : ((later x) >>=ᵖ (λ s -> later (ceval-while c b s))) ⇓ s') 
    -> s ∻ s'
  while-∻-later {x} c b s s' f (laterₗ h⇓) {id} (z , id∈s) 
   with (force x) in eq-fx
  ... | now nothing 
   rewrite eq-fx  
   with h⇓
  ... | now ()
  while-∻-later {x} c b s s' f (laterₗ (laterₗ w⇓)) {id} (z , id∈s) 
   | now (just sⁱ)
   with (beval b sⁱ) in eq-b
  ... | nothing rewrite eq-b
   with w⇓
  ... | now ()
  while-∻-later {x} c b s s' f (laterₗ (laterₗ w⇓)) {id} (z , id∈s) | now (just sⁱ) | just false 
   rewrite eq-b
   with w⇓
  ... | now refl = f sⁱ (laterₗ (≡=>≋ eq-fx)) (z , id∈s)
  while-∻-later {x} c b s s' f (laterₗ (laterₗ w⇓)) {id} (z , id∈s) | now (just sⁱ) | just true 
   rewrite eq-b 
   with (bindxf⇓=>x⇓ {x = ceval c sⁱ} {f = λ s -> later (ceval-while c b s)} w⇓) 
  ... | sⁱ' , cⁱ⇓sⁱ' 
   with (f sⁱ (laterₗ (≡=>≋ eq-fx)) {id})
  ... | s⊑sⁱ 
   with (while-∻ c b sⁱ s' (λ { s₁ sⁱ₁ c⇓sⁱ {id} (z' , id∈s₁) → ceval⇓=>∻ c s₁ sⁱ₁ c⇓sⁱ {id} (z' , id∈s₁)}) w⇓ {id})
  ... | sⁱ⊑s' = ∻-trans s⊑sⁱ sⁱ⊑s' {id} (z , id∈s) 
  while-∻-later {x} c b s s' f (laterₗ h⇓) {id} (z , id∈s) 
   | later x₁ = while-∻-later {x₁} c b s s' (λ { sⁱ x₂ x₃ → f sⁱ (laterₗ (≡=>⇓ eq-fx x₂)) x₃}) h⇓ {id} (z , id∈s)
  
  while-∻ : ∀ (c : Command) (b : BExp) (s s' : Store) (f : ∀ (s sⁱ : Store) -> (ceval c s) ⇓ sⁱ -> s ∻ sⁱ)
   (h⇓ : ((ceval c s) >>=ᵖ (λ s -> later (ceval-while c b s))) ⇓ s') -> s ∻ s'
  while-∻ c b s s' f h⇓ {id} 
   with (ceval c s) in eq-c
  ... | now nothing 
   rewrite eq-c 
   with h⇓
  ... | now ()
  while-∻ c b s s' f (laterₗ w⇓) {id} | now (just sⁱ) 
   rewrite eq-c 
   with (beval b sⁱ) in eq-b
  ... | nothing 
   rewrite eq-b 
   with w⇓
  ... | now ()
  while-∻ c b s s' f (laterₗ w⇓) {id} | now (just sⁱ) | just true 
   rewrite eq-b = ∻-trans {s} {sⁱ} {s'} (f s sⁱ (≡=>≋ eq-c)) (while-∻ c b sⁱ s' f w⇓) {id}
  while-∻ c b s s' f (laterₗ w⇓) {id} | now (just sⁱ) | just false 
   rewrite eq-b
   with w⇓
  ... | now refl = f s sⁱ (≡=>≋ eq-c) {id}
  while-∻ c b s s' f h⇓ {id} 
   | later x = while-∻-later {x} c b s s' (λ { sⁱ x₁ x₂ → f s sⁱ (≡=>⇓ eq-c x₁) x₂}) h⇓

 ceval⇓=>∻ : ∀ (c : Command) (s s' : Store) (h⇓ : (ceval c s) ⇓ s') -> s ∻ s'
 ceval⇓=>∻ skip s .s (now refl) x = x
 ceval⇓=>∻ (assign id a) s s' h⇓ {id₁} x
  with (aeval a s) in eq-aeval
 ... | just v with h⇓
 ... | now refl 
  with (id == id₁) in eq-id
 ... | true rewrite eq-id = v , refl 
 ... | false rewrite eq-id = x
 ceval⇓=>∻ (assign id a) s s' h⇓ {id₁} x
  | nothing rewrite eq-aeval 
  with h⇓
 ... | now ()
 ceval⇓=>∻ (ifelse b cᵗ cᶠ) s s' h⇓ x 
  with (beval b s) in eq-b
 ... | just true rewrite eq-b = ceval⇓=>∻ cᵗ s s' h⇓ x 
 ... | just false rewrite eq-b = ceval⇓=>∻ cᶠ s s' h⇓ x 
 ... | nothing with h⇓
 ... | now () 
 ceval⇓=>∻ (seq c₁ c₂) s s' h⇓ {id} 
  with (bindxf⇓=>x⇓ {x = ceval c₁ s} {f = ceval c₂} h⇓)
 ... | sⁱ , c₁⇓sⁱ 
  with (bindxf⇓-x⇓=>f⇓ {x = ceval c₁ s} {f = ceval c₂} h⇓ c₁⇓sⁱ)
 ... | c₂⇓s' = ∻-trans (ceval⇓=>∻ c₁ s sⁱ c₁⇓sⁱ {id}) (ceval⇓=>∻ c₂ sⁱ s' c₂⇓s' {id}) {id}
 ceval⇓=>∻ (while b c) s s' h⇓ {id} x 
  with (beval b s) in eq-b
 ... | just false with h⇓
 ... | now refl = x
 ceval⇓=>∻ (while b c) s s' h⇓ {id} x
  | just true rewrite eq-b = while-∻ c b s s' (λ s₁ s₂ h -> ceval⇓=>∻ c s₁ s₂ h) h⇓ {id} x
 ceval⇓=>∻ (while b c) s s' h⇓ {id} x | nothing 
  with h⇓
 ... | now ()


ceval⇓=>⊆ : ∀ (c : Command) (s s' : Store) (h⇓ : (ceval c s) ⇓ s') -> (dom s) ⊆ (dom s')
ceval⇓=>⊆ c s s' h⇓ x x-in-s₁ 
 with (ceval⇓=>∻ c s s' h⇓)
... | s⊑s' with (s x)  in eq-sx
... | just x₁ 
 with (s⊑s' {x} (x₁ , eq-sx))
... | fst , snd rewrite snd = refl

ceval⇓=>sc⊆s' :  ∀ (c : Command) (s s' : Store) (h⇓ : (ceval c s) ⇓ s') -> (dom s ∪ (cvars c)) ⊆ (dom s')
ceval⇓=>sc⊆s' skip s .s (now refl) x x-in-s₁ rewrite (cvars-skip) rewrite (∨-identityʳ (dom s x)) = x-in-s₁
ceval⇓=>sc⊆s' (assign id a) s s' h⇓ x x-in-s₁ 
 with (aeval a s)
... | nothing 
 with h⇓
... | now ()
ceval⇓=>sc⊆s' (assign id a) s s' h⇓ x x-in-s₁ 
 | just v 
 with h⇓
... | now refl
 with (id == x) in eq-id
... | true = refl
... | false rewrite eq-id rewrite (∨-identityʳ (dom s x)) 
 with s x in eq-sx
... | just x₁ rewrite eq-sx = refl
ceval⇓=>sc⊆s' (ifelse b cᵗ cᶠ) s s' h⇓ x x-in-s₁ 
 with (beval b s) in eq-b 
... | nothing 
 with h⇓
... | now ()
ceval⇓=>sc⊆s' (ifelse b cᵗ cᶠ) s s' h⇓ x x-in-s₁ 
 | just false rewrite eq-b = ceval⇓=>sc⊆s' cᶠ s s' h⇓ x (h {dom s x} {cvars cᵗ x} {cvars cᶠ x} x-in-s₁)
 where
  h : {b1 b2 b3 : Bool} (h : b1 ∨ (b2 ∧ b3) ≡ true) -> b1 ∨ b3 ≡ true
  h {false} {b2} {true} h₁ = refl
  h {false} {false} {false} h₁ = case h₁ of λ () 
  h {false} {true} {false} h₁ = case h₁ of λ () 
  h {true} {b2} {b3} h₁ = refl
ceval⇓=>sc⊆s' (ifelse b cᵗ cᶠ) s s' h⇓ x x-in-s₁ 
 | just true rewrite eq-b = ceval⇓=>sc⊆s' cᵗ s s' h⇓ x (h {dom s x} {cvars cᵗ x} {cvars cᶠ x}  x-in-s₁)
 where 
  h : {b1 b2 b3 : Bool} (h : b1 ∨ (b2 ∧ b3) ≡ true) -> b1 ∨ b2 ≡ true
  h {false} {true} {b3} h₁ = refl
  h {true} {b2} {b3} h₁ = refl
ceval⇓=>sc⊆s' (seq c₁ c₂) s s' h⇓ x x-in-s₁
 with (bindxf⇓=>x⇓ {x = ceval c₁ s} {f = ceval c₂} h⇓)
... | sⁱ , c₁⇓sⁱ 
 with (bindxf⇓-x⇓=>f⇓ {x = ceval c₁ s} {f = ceval c₂} h⇓ c₁⇓sⁱ)
... | c₂⇓s' 
 with (ceval⇓=>sc⊆s' c₁ s sⁱ c₁⇓sⁱ x)
... | n 
 with (ceval⇓=>sc⊆s' c₂ sⁱ s' c₂⇓s' x)
... | n'
 with (dom s x) | (cvars c₁ x) | (cvars c₂ x)
... | false | false | true rewrite (∨-zeroʳ (dom sⁱ x)) = n' refl 
... | false | true | false rewrite (∨-zeroˡ (false)) rewrite (∨-identityʳ (dom sⁱ x)) = n' (n refl)
... | false | true | true rewrite (∨-zeroˡ (false)) rewrite (∨-zeroʳ (dom sⁱ x)) = n' refl
... | true | n2 | n3 rewrite (∨-zeroˡ (true)) rewrite (n refl) rewrite (∨-identityʳ (dom sⁱ x)) = n' refl
ceval⇓=>sc⊆s' (while b c) s s' h⇓ x x-in-s₁ rewrite (cvars-while {b} {c}) 
 rewrite (∨-identityʳ (dom s x)) = ceval⇓=>⊆ (while b c) s s' h⇓ x x-in-s₁ 
