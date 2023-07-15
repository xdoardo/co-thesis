------------------------------------------------------------------------
-- Definite initialization analysis for IMP and its properties
------------------------------------------------------------------------
module Imp.Analysis.DefiniteInitialization where 

open import Data.Bool
open import Imp.Syntax 
open import Data.Maybe 
open import Codata.Sized.Thunk 
open import Data.String hiding (_≈_)
open import Imp.Semantics.BigStep.Functional
---

adia : (a : AExp) -> (s : VarsSet) -> Bool 
adia (const n) s = true 
adia (var id) s = s id
adia (plus a a₁) s = (adia a s) ∧ (adia a₁ s)

bdia : (b : BExp) -> (s : VarsSet) -> Bool 
bdia (const b) s = true 
bdia (le a₁ a₂) s =  (adia a₁ s) ∧ (adia a₂ s)
bdia (BExp.not b) s = bdia b s
bdia (and b b₁) s = (bdia b s) ∧ (bdia b₁ s)

private
 cdia-inner : (c : Command) -> (s : VarsSet) -> Maybe VarsSet
 cdia-inner skip s = just ∅ 
 cdia-inner (assign id a) s with (adia a s) 
 ... | false = nothing 
 ... | true = just (id ↦ s)
 cdia-inner (seq c c₁) s = (cdia-inner c s) >>= λ s₁ -> (cdia-inner c s₁) >>= just
 cdia-inner (ifelse b c c₁) s with (bdia b s) 
 ... | false = nothing 
 ... | true = (cdia-inner c s) >>= λ s₁ -> (cdia-inner c s) >>= λ s₂ -> just (s₁ ∩ s₂)
 cdia-inner (while b c) s with (bdia b s) 
 ... | false = nothing 
 ... | true =  cdia-inner c s >>= λ _ -> just s

cdia : (c : Command) -> (s : VarsSet) -> Bool 
cdia c s with (cdia-inner c s)
... | just x = true
... | nothing = false 


data DiaRel : VarsSet -> Command -> VarsSet -> Set where 
 skip : ∀ (v : VarsSet) -> DiaRel v (skip) v
 assign : ∀ a v id (a⊆s : (avars a) ⊆ v) -> DiaRel v (assign id a) (id ↦ v)
 seq : ∀ v₁ v₂ v₃ c₁ c₂ -> (relc₁ : DiaRel v₁ c₁ v₂) -> 
  (relc₂ : DiaRel v₂ c₂ v₃) -> DiaRel v₁ (seq c₁ c₂) v₃ 
 if : ∀ b v vᵗ vᶠ cᵗ cᶠ (b⊆s : (bvars b) ⊆ v) -> (relcᶠ : DiaRel v cᶠ vᶠ) -> 
  (relcᵗ : DiaRel v cᵗ vᵗ) -> DiaRel v (ifelse b cᵗ cᶠ) (vᵗ ∩ vᶠ)
 while : ∀ b v v₁ c -> (b⊆s : (bvars b) ⊆ v) -> (relc : DiaRel v c v₁) -> DiaRel v (while b c) v₁

--------------------------------------------------
-- Properties of definite initialization analysis 
--------------------------------------------------
module _ where
 
 open import Data.And
 open import Data.Empty
 open import Data.Product
 open import Function.Base
 open import Codata.Sized.Delay
 open import Codata.Sized.Partial
 open import Codata.Sized.Partial.Bisimilarity
 open import Relation.Binary.PropositionalEquality
 open import Codata.Sized.Partial.Bisimilarity.Relation.Binary.Equivalence hiding (sym)


 postulate
  true-or-false : true ∨ false ≡ false -> ⊥
  just-is-nothing : ∀ {A : Set} {v : A} -> just v ≡ nothing -> ⊥ 

  rel-inc : ∀ s s' c -> (relc : DiaRel s c s') -> s ⊆ s'
  rel-⊆-ceval : ∀ {i v v' c s s'} -> (relc : DiaRel v c v') -> (v⊆s : v ⊆ dom s) -> 
   (eq-ceval : i ⊢ (ceval c s) ≈ now (just s')) -> v' ⊆ dom s'


 -- From `DiaRel` to `cdia`
 rel-dia : ∀ s s' c -> (relc : DiaRel s c s') -> 
  And (s' ≡ (s ∪ (cvars c))) (cdia c s ≡ true)
 rel-dia s .s skip (skip .s) with (cvars skip) 
 ... | v = both {! !} _≡_.refl
 rel-dia s s' (assign id₁ a) relc = {! !}
 rel-dia s s' (seq c c₁) relc = {! !}
 rel-dia s s' (ifelse b c c₁) relc = {! !}
 rel-dia s s' (while b c) relc = {! !}

 -- From `cdia` to `DiaRel`
 dia-rel : ∀ s c -> (diat : cdia c s ≡ true) -> DiaRel s c (s ∪ (cvars c))
 dia-rel = ?

 -- Definitely initialized arithmetic expressions cannot go wrong.
 adia-safe : ∀ (s : Store) (a : AExp) -> (vars⊆s : avars a ⊆ (dom s)) -> 
  ((eq-aeval : (aeval a s) ≡ nothing) -> ⊥)
 adia-safe s (var id) vars⊆s eq-aeval  
  with (avars (var id)) id in eq-avars-id
 ... | false rewrite (==-refl {id}) = true-or-false eq-avars-id 
 ... | true with (in-dom-has-value {s} {id} (vars⊆s id eq-avars-id))
 ... | v , eq-sid rewrite eq-sid = just-is-nothing eq-aeval
 adia-safe s (plus a a₁) vars⊆s x with (aeval a s) in eq-aeval
 ... | nothing = 
  adia-safe s a (⊆-trans (⊑ᵃ=>⊆ a (plus a a₁) (plus-l a a₁)) vars⊆s) eq-aeval
 ... | just x₁ with (aeval a₁ s) in eq-aeval₁ 
 ... | nothing = 
  adia-safe s a₁ (⊆-trans ((⊑ᵃ=>⊆ a₁ (plus a a₁) (plus-r a a₁)) ) vars⊆s) eq-aeval₁

 -- Definitely initialized boolean expressions cannot go wrong.
 bdia-safe : ∀ (s : Store) (b : BExp) -> (vars⊆s : bvars b ⊆ (dom s)) -> 
  ((eq-beval : (beval b s) ≡ nothing)-> ⊥)
 bdia-safe s (le a₁ a₂) vars⊆s eq-beval with (aeval a₁ s) in eq-aeval₁
 ... | nothing = adia-safe s a₁ (⊆-trans (⊑ᵇᵃ=>⊆ a₁ (le a₁ a₂) (le-l a₁ a₂)) vars⊆s) eq-aeval₁ 
 ... | just x with (aeval a₂ s) in eq-aeval₂
 ... | nothing = adia-safe s a₂ (⊆-trans (⊑ᵇᵃ=>⊆ a₂ (le a₁ a₂) (le-r a₁ a₂)) vars⊆s) eq-aeval₂
 bdia-safe s (BExp.not b) vars⊆s eq-beval 
  with (beval b s) in eq-beval₁
 ... | nothing = bdia-safe s b vars⊆s eq-beval₁
 bdia-safe s (and b b₁) vars⊆s eq-beval with (beval b s) in eq-beval₁
 ... | nothing = bdia-safe s b (⊆-trans (⊑ᵇᵇ=>⊆ b (and b b₁) (and-l b b₁)) vars⊆s) eq-beval₁ 
 ... | just x with (beval b₁ s) in eq-beval₂
 ... | nothing = bdia-safe s b₁ (⊆-trans (⊑ᵇᵇ=>⊆ b₁ (and b b₁) (and-r b b₁)) vars⊆s) eq-beval₂

 -- Definitely initialized commands cannot go wrong.
 cdia-safe : ∀ {i} (s : Store) (v v' : VarsSet) (c : Command) -> 
  (c⊆s : v ⊆ (dom s)) -> (relc : DiaRel v c v') -> ((bisim : i ⊢ ceval c s ≈ fail) -> ⊥)
 cdia-safe s v .(id₁ ↦ v) (assign id₁ a) c⊆s (assign .a .v .id₁ a⊆s) bisim with (aeval a s) in eq-aeval
 ... | nothing = adia-safe s a (λ x x-in-s₁ → c⊆s x (a⊆s x x-in-s₁)) eq-aeval 
 cdia-safe s v₁ v₃ (seq c₁ c₂) c⊆s (seq .v₁ v₂ .v₃ .c₁ .c₂ relc₁ relc₂) bisim with (ceval c₁ s) in eq-ceval₁
 ... | now nothing = cdia-safe s v₁ v₂ c₁ c⊆s relc₁ (≡=>≈ eq-ceval₁)
 ... | now (just s') with (ceval c₂ s') in eq-ceval₂
 ... | now nothing = 
  cdia-safe s' v₂ v₃ c₂ (rel-⊆-ceval relc₁ c⊆s (≡=>≈ eq-ceval₁)) relc₂ (≡=>≈ eq-ceval₂)
 ... | later x rewrite (sym eq-ceval₂) = 
  cdia-safe s' v₂ v₃ c₂ (rel-⊆-ceval relc₁ c⊆s (≡=>≈ eq-ceval₁)) relc₂ bisim
 cdia-safe s v₁ v₃ (seq c₁ c₂) c⊆s (seq .v₁ v₂ .v₃ .c₁ .c₂ relc₁ relc₂) bisim 
  | later x = ? 
 cdia-safe s v v' (ifelse b c c₁) c⊆s relc bisim = {! !}
 cdia-safe s v v' (while b c) c⊆s relc bisim = {! !}
