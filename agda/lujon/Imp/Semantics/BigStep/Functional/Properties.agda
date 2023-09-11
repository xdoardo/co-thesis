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
open import Codata.Sized.Partial
open import Data.Bool.Properties
open import Codata.Sized.Delay hiding (_⇓)
open import Imp.Semantics.BigStep.Functional
open import Codata.Sized.Partial.Bisimilarity
open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Codata.Sized.Partial.Effectful using () renaming (bind to _>>=ᵖ_)
open import Codata.Sized.Partial.Bisimilarity.Properties
open import Codata.Sized.Partial.Relation.Binary.Convergence 
open import Data.String using (String ; _==_) renaming (_≟_ to _≟ₛ_)
open import Codata.Sized.Partial.Bisimilarity.Relation.Binary.Equivalence 
 renaming (sym to psym ; refl to prefl ; trans to ptrans)
--

⇓=>≡ : ∀ {a} {A : Set a} (x : Delay (Maybe A) ∞) (y z : A) (h : x ⇓ z) (h₁ : x ≡ (now (just y))) -> (z ≡ y)
⇓=>≡ .(now (just y)) y z (nowj h-≡) refl rewrite h-≡ = refl


mutual 
 private
  while-⊑ᵘ-later :  ∀ {x : Thunk (Delay (Maybe Store)) ∞} (c : Command) (b : BExp) (s s' : Store)  
   (f : ∀ (sⁱ : Store) -> later x ⇓ sⁱ -> s ⊑ᵘ sⁱ) (h⇓ : ((later x) >>=ᵖ (λ s -> later (ceval-while c b s))) ⇓ s') 
    -> s ⊑ᵘ s'
  while-⊑ᵘ-later {x} c b s s' f (laterₗ h⇓) {id} (z , id∈s) 
   with (force x) in eq-fx
  ... | now (just sⁱ) rewrite eq-fx 
   with h⇓
  ... | laterₗ w⇓ 
   with (beval b sⁱ) in eq-b 
  ... | just false with w⇓
  ... | nowj refl = f sⁱ (laterₗ (≡=>≈ eq-fx)) (z , id∈s)
  while-⊑ᵘ-later {x} c b s s' f (laterₗ h⇓) {id} (z , id∈s) | now (just sⁱ) | laterₗ w⇓
   | just true rewrite eq-b 
   with (bindxf⇓=>x⇓ {x = ceval c sⁱ} {f = λ s -> later (ceval-while c b s)} w⇓) 
  ... | sⁱ' , cⁱ⇓sⁱ' 
   with (f sⁱ (laterₗ (≡=>≈ eq-fx)) {id})
  ... | s⊑sⁱ 
   with (while-⊑ᵘ c b sⁱ s' (λ { s₁ sⁱ₁ c⇓sⁱ {id} (z' , id∈s₁) → ceval⇓=>⊑ᵘ c s₁ sⁱ₁ c⇓sⁱ {id} (z' , id∈s₁)}) w⇓ {id})
  ... | sⁱ⊑s' = ⊑ᵘ-trans s⊑sⁱ sⁱ⊑s' {id} (z , id∈s) 
  while-⊑ᵘ-later {x} c b s s' f (laterₗ h⇓) {id} (z , id∈s) 
   | later x₁ = while-⊑ᵘ-later {x₁} c b s s' (λ { sⁱ x₂ x₃ → f sⁱ (laterₗ (≡=>⇓ eq-fx x₂)) x₃}) h⇓ {id} (z , id∈s)
  
  
  while-⊑ᵘ : ∀ (c : Command) (b : BExp) (s s' : Store) (f : ∀ (s sⁱ : Store) -> (ceval c s) ⇓ sⁱ -> s ⊑ᵘ sⁱ)
   (h⇓ : ((ceval c s) >>=ᵖ (λ s -> later (ceval-while c b s))) ⇓ s') -> s ⊑ᵘ s'
  while-⊑ᵘ c b s s' f h⇓ {id}
   with (ceval c s) in eq-c
  ... | now (just sⁱ) 
   with (f s sⁱ (≡=>≈ eq-c))
  ... | s⊑sⁱ rewrite eq-c 
   with h⇓ 
  ... | laterₗ w⇓ 
   with (beval b sⁱ) in eq-b
  ... | just false rewrite eq-b with w⇓
  ... | nowj refl = s⊑sⁱ {id}
  while-⊑ᵘ c b s s' f h⇓ {id} | now (just sⁱ) | s⊑sⁱ | laterₗ w⇓ | just true 
   rewrite eq-b
   = ⊑ᵘ-trans {s} {sⁱ} {s'} s⊑sⁱ (while-⊑ᵘ c b sⁱ s' f w⇓) {id}
  while-⊑ᵘ c b s s' f h⇓
   | later x 
   with h⇓
  ... | laterₗ w⇓ = while-⊑ᵘ-later {x} c b s s' (λ { sⁱ x₁ x₂ → f s sⁱ (≡=>⇓ eq-c x₁) x₂}) h⇓

 ceval⇓=>⊑ᵘ : ∀ (c : Command) (s s' : Store) (h⇓ : (ceval c s) ⇓ s') -> s ⊑ᵘ s'
 ceval⇓=>⊑ᵘ skip s .s (nowj refl) x = x
 ceval⇓=>⊑ᵘ (assign id a) s s' h⇓ {id₁} x  
  with (aeval a s)
 ... | just v 
  with h⇓
 ... | nowj refl 
  with (id == id₁) in eq-id
 ... | true rewrite eq-id = v , refl 
 ... | false rewrite eq-id = x
 ceval⇓=>⊑ᵘ (ifelse b cᵗ cᶠ) s s' h⇓ x 
  with (beval b s) in eq-b
 ... | just true rewrite eq-b = ceval⇓=>⊑ᵘ cᵗ s s' h⇓ x 
 ... | just false rewrite eq-b = ceval⇓=>⊑ᵘ cᶠ s s' h⇓ x 
 ceval⇓=>⊑ᵘ (seq c₁ c₂) s s' h⇓ {id} 
  with (bindxf⇓=>x⇓ {x = ceval c₁ s} {f = ceval c₂} h⇓)
 ... | sⁱ , c₁⇓sⁱ 
  with (bindxf⇓-x⇓=>f⇓ {x = ceval c₁ s} {f = ceval c₂} h⇓ c₁⇓sⁱ)
 ... | c₂⇓s' = ⊑ᵘ-trans (ceval⇓=>⊑ᵘ c₁ s sⁱ c₁⇓sⁱ {id}) (ceval⇓=>⊑ᵘ c₂ sⁱ s' c₂⇓s' {id}) {id}
 ceval⇓=>⊑ᵘ (while b c) s s' h⇓ {id} x 
  with (beval b s) in eq-b
 ... | just false with h⇓
 ... | nowj refl = x
 ceval⇓=>⊑ᵘ (while b c) s s' h⇓ {id} x
  | just true rewrite eq-b = while-⊑ᵘ c b s s' (λ s₁ s₂ h -> ceval⇓=>⊑ᵘ c s₁ s₂ h) h⇓ {id} x

ceval⇓=>⊆ : ∀ (c : Command) (s s' : Store) (h⇓ : (ceval c s) ⇓ s') -> (dom s) ⊆ (dom s')
ceval⇓=>⊆ c s s' h⇓ x x-in-s₁ 
 with (ceval⇓=>⊑ᵘ c s s' h⇓)
... | s⊑s' with (s x)  in eq-sx
... | just x₁ 
 with (s⊑s' {x} (x₁ , eq-sx))
... | fst , snd rewrite snd = refl

ceval⇓=>sc⊆s' :  ∀ (c : Command) (s s' : Store) (h⇓ : (ceval c s) ⇓ s') -> (dom s ∪ (cvars c)) ⊆ (dom s')
ceval⇓=>sc⊆s' skip s .s (nowj refl) x x-in-s₁ rewrite (cvars-skip) rewrite (∨-identityʳ (dom s x)) = x-in-s₁
ceval⇓=>sc⊆s' (assign id a) s s' h⇓ x x-in-s₁ 
 with (aeval a s)
... | just v 
 with h⇓
... | nowj refl
 with (id == x) in eq-id
... | true = refl
... | false rewrite eq-id rewrite (∨-identityʳ (dom s x)) 
 with s x in eq-sx
... | just x₁ rewrite eq-sx = refl
ceval⇓=>sc⊆s' (ifelse b cᵗ cᶠ) s s' h⇓ x x-in-s₁ 
 with (beval b s) in eq-b 
... | just false rewrite eq-b = ceval⇓=>sc⊆s' cᶠ s s' h⇓ x (h {dom s x} {cvars cᵗ x} {cvars cᶠ x} x-in-s₁)
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
... | false | true | false rewrite (∨-zeroˡ (false)) = n' ? 
... | false | true | true = {! !}
... | true | n2 | n3 = {! !}
ceval⇓=>sc⊆s' (while b c) s s' h⇓ x x-in-s₁ rewrite (cvars-while {b} {c}) 
 rewrite (∨-identityʳ (dom s x)) = ceval⇓=>⊆ (while b c) s s' h⇓ x x-in-s₁ 
