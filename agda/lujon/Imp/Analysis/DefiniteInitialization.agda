------------------------------------------------------------------------
-- Definite initialization analysis for IMP and its properties
------------------------------------------------------------------------
module Imp.Analysis.DefiniteInitialization where 

open import Size
open import Data.Or
open import Data.Bool
open import Imp.Syntax 
open import Data.Maybe 
open import Data.Product
open import Codata.Sized.Thunk 
open import Data.Bool.Properties
open import Codata.Sized.Partial
open import Data.String hiding (_≈_)
open import Function using (case_of_)
open import Imp.Semantics.BigStep.Functional
open import Codata.Sized.Delay hiding (bind ; _⇓)
open import Codata.Sized.Partial.Relation.Binary.Convergence 
---


data Dia : VarsSet -> Command -> VarsSet -> Set where 
 skip : ∀ (v : VarsSet) -> Dia v (skip) v
 assign : ∀ a v id (a⊆v : (avars a) ⊆ v) -> Dia v (assign id a) (id ↦ v)
 seq : ∀ v₁ v₂ v₃ c₁ c₂ -> (relc₁ : Dia v₁ c₁ v₂) -> 
  (relc₂ : Dia v₂ c₂ v₃) -> Dia v₁ (seq c₁ c₂) v₃ 
 if : ∀ b v vᵗ vᶠ cᵗ cᶠ (b⊆v : (bvars b) ⊆ v) -> (relcᶠ : Dia v cᶠ vᶠ) -> 
  (relcᵗ : Dia v cᵗ vᵗ) -> Dia v (ifelse b cᵗ cᶠ) (vᵗ ∩ vᶠ)
 while : ∀ b v v₁ c -> (b⊆s : (bvars b) ⊆ v) -> (relc : Dia v c v₁) -> Dia v (while b c) v

--------------------------------------------------
-- Properties of definite initialization analysis 
--------------------------------------------------
module _ where


 open import Data.Empty
 open import Data.Integer
 open import Codata.Sized.Thunk
 open import Codata.Sized.Partial.Effectful 
 open import Codata.Sized.Partial.Bisimilarity
 open import Relation.Binary.PropositionalEquality
 open import Imp.Semantics.BigStep.Functional.Properties
 open import Codata.Sized.Partial.Bisimilarity.Relation.Binary.Equivalence using (≡=>≈)


 adia-sound : ∀ (a : AExp) (s : Store) -> (dia : avars a ⊆ dom s) -> (∃ λ v -> aeval a s ≡ just v)
 adia-sound (const n) s dia = n , refl
 adia-sound (var id) s dia 
  with (avars (var id) id) in eq-avars-id
 ... | false rewrite (==-refl {id}) with eq-avars-id
 ... | ()
 adia-sound (var id) s dia | true = in-dom-has-value {s} {id} (dia id eq-avars-id)
 adia-sound (plus a₁ a₂) s dia 
  with (adia-sound a₁ s (⊆-trans (⊏ᵃ=>⊆ a₁ (plus a₁ a₂) (plus-l a₁ a₂)) dia))
 ... | v₁ , eq-aev-a₁ 
  with (adia-sound a₂ s (⊆-trans (⊏ᵃ=>⊆ a₂ (plus a₁ a₂) (plus-r a₁ a₂)) dia))
 ... | v₂ , eq-aev-a₂ rewrite eq-aev-a₁ rewrite eq-aev-a₂ = v₁ + v₂ , refl

 bdia-sound : ∀ (b : BExp) (s : Store) -> (dia : bvars b ⊆ dom s) -> (∃ λ v -> beval b s ≡ just v)
 bdia-sound (const b) s dia = b , refl
 bdia-sound (le a₁ a₂) s dia 
  with (adia-sound a₁ s (⊆-trans (⊏ᵇᵃ=>⊆ a₁ (le a₁ a₂) (le-l a₁ a₂)) dia)) 
   | (adia-sound a₂ s (⊆-trans (⊏ᵇᵃ=>⊆ a₂ (le a₁ a₂) (le-r a₁ a₂)) dia))
 ... | v₁ , eq-a₁ | v₂ , eq-a₂ rewrite eq-a₁ rewrite eq-a₂ = (v₁ ≤ᵇ v₂) , refl
 bdia-sound (BExp.not b) s dia 
  with (bdia-sound b s (⊆-trans (⊏ᵇᵇ=>⊆ b (BExp.not b) (_⊏ᵇ_.not b)) dia))
 ... | v , eq-b rewrite eq-b = (Data.Bool.not v) , refl
 bdia-sound (and b₁ b₂) s dia
  with (bdia-sound b₁ s (⊆-trans (⊏ᵇᵇ=>⊆ b₁ (and b₁ b₂) (and-l b₁ b₂)) dia)) 
   | (bdia-sound b₂ s (⊆-trans (⊏ᵇᵇ=>⊆ b₂ (and b₁ b₂) (and-r b₁ b₂)) dia))
 ... | v₁ , eq-b₁ | v₂ , eq-b₂ rewrite eq-b₁ rewrite eq-b₂ = (v₁ ∧ v₂) , refl

 
 dia=>cvars : ∀ {v₁ v₂ : VarsSet} {c : Command} (h-dia : Dia v₁ c v₂) -> v₂ ≡ (v₁ ∪ (cvars c))
 dia=>cvars {v₁} {.v₁} {skip} (skip .v₁) rewrite (cvars-skip) = if-ext λ { x → sym (∨-identityʳ (v₁ x)) } 
 dia=>cvars {v₁} {.(id ↦ v₁)} {assign id a} (assign .a .v₁ .id a⊆v) = ↦-is-∪ {id} {v₁}  
 dia=>cvars {v₁} {v₃} {seq c₁ c₂} (seq .v₁ v₂ .v₃ .c₁ .c₂ h-dia₁ h-dia₂) 
  rewrite (cvars-seq {c₁} {c₂})
  rewrite (dia=>cvars h-dia₁)
  rewrite (dia=>cvars h-dia₂)
  = if-ext λ { x → ∨-assoc (v₁ x) (cvars c₁ x) (cvars c₂ x) } 
 dia=>cvars {v₁} {.(vᵗ ∩ vᶠ)} {ifelse b c c₁} (if .b .v₁ vᵗ vᶠ .c .c₁ b⊆v h-dia h-dia₁) 
  rewrite (cvars-if {b} {c} {c₁})
  rewrite (dia=>cvars h-dia₁)
  rewrite (dia=>cvars h-dia)
  = if-ext λ { x -> h {v₁ x} {cvars c x} {cvars c₁ x}} 
  where 
   h : {b₁ b₂ b₃ : Bool} -> (b₁ ∨ b₂) ∧ (b₁ ∨ b₃) ≡ b₁ ∨ (b₂ ∧ b₃)
   h {false} {b₂} {b₃} = refl
   h {true} {false} {false} = refl
   h {true} {false} {true} = refl
   h {true} {true} {false} = refl
   h {true} {true} {true} = refl
 dia=>cvars {v₁} {.v₁} {while b c} (while .b .v₁ v₂ .c b⊆s h-dia) 
  rewrite (cvars-while {b} {c})
  = if-ext λ { x → sym (∨-identityʳ (v₁ x)) } 

 dia-⊆ : ∀ {v₁ v₂ : VarsSet} {c : Command} (h-dia : Dia v₁ c v₂) -> v₁ ⊆ v₂
 dia-⊆ {v₁} {.v₁} {skip} (skip .v₁) x x-in-s₁ = x-in-s₁
 dia-⊆ {v₁} {.(id ↦ v₁)} {assign id a} (assign .a .v₁ .id a⊆v) x x-in-s₁ = ↦=>⊆ {id} {v₁} x x-in-s₁ 
 dia-⊆ {v₁} {v₃} {seq c₁ c₂} (seq .v₁ v₂ .v₃ .c₁ .c₂ h-dia₁ h-dia₂)  
  = (⊆-trans (dia-⊆ {v₁} {v₂} {c₁} h-dia₁) (dia-⊆ {v₂} {v₃} {c₂} h-dia₂)) 
 dia-⊆ {v₁} {.(vᵗ ∩ vᶠ)} {ifelse b c c₁} (if .b .v₁ vᵗ vᶠ .c .c₁ b⊆v h-dia h-dia₁) 
  = ⊆=>∩ {v₁} {vᵗ} {vᶠ} (dia-⊆ h-dia₁) (dia-⊆ h-dia)
 dia-⊆ {v₁} {.v₁} {while b c} (while .b .v₁ v₂ .c b⊆s h-dia) x x-in-s₁ = x-in-s₁ 

 dia-ceval=>⊆ : ∀ {v₁ v₂ : VarsSet} {s₁ s₂ : Store} {c : Command} (dia : Dia v₁ c v₂) 
   -> (v₁⊆s₁ : v₁ ⊆ dom s₁) -> (h⇓ : (ceval c s₁) ⇓ s₂) -> v₂ ⊆ dom s₂
 dia-ceval=>⊆ {v₁} {v₂} {s₁} {s₂} {c} dia v₁⊆s₁ h⇓ x x-in-v₁ rewrite (dia=>cvars dia) = 
  let 
   v₂⊆s₁c = ⊆-∪=>⊆ {v₁} {dom s₁} {cvars c} v₁⊆s₁ x 
   s₁c⊆s₂ = ceval⇓=>sc⊆s' c s₁ s₂ h⇓ x
  in s₁c⊆s₂ (v₂⊆s₁c x-in-v₁)
 
 mutual 
  dia-sound : ∀ (c : Command) (s : Store) (v v' : VarsSet) (dia : Dia v c v') (v⊆s : v ⊆ dom s)
   -> (h-err : (ceval c s) ↯) -> ⊥
  dia-sound (assign id a) s v .(id ↦ v) (assign .a .v .id a⊆v) v⊆s h-err 
   with (adia-sound a s (⊆-trans a⊆v v⊆s))
  ... | a' , eq-aeval rewrite eq-aeval rewrite eq-aeval with (h-err) 
  ... | ()
  dia-sound (ifelse b cᵗ cᶠ) s v .(vᵗ ∩ vᶠ) (if .b .v vᵗ vᶠ .cᵗ .cᶠ b⊆v diaᶠ diaᵗ) v⊆s h-err 
    with (bdia-sound b s λ x x-in-s₁ → v⊆s x (b⊆v x x-in-s₁))
  ... | false , eq-beval rewrite eq-beval rewrite eq-beval = dia-sound cᶠ s v vᶠ diaᶠ v⊆s h-err
  dia-sound (ifelse b cᵗ cᶠ) s v .(vᵗ ∩ vᶠ) (if .b .v vᵗ vᶠ .cᵗ .cᶠ b⊆v diaᶠ diaᵗ) v⊆s h-err 
   | true , eq-beval rewrite eq-beval rewrite eq-beval = dia-sound cᵗ s v vᵗ diaᵗ v⊆s h-err
  dia-sound (seq c₁ c₂) s v₁ v₃ dia v⊆s h-err with dia
  ... | seq .v₁ v₂ .v₃ .c₁ .c₂ dia-c₁ dia-c₂ with (ceval c₁ s) in eq-ceval-c₁
  ... | now nothing = dia-sound c₁ s v₁ v₂ dia-c₁ v⊆s (≡=>≈ eq-ceval-c₁) 
  ... | now (just s') rewrite eq-ceval-c₁ = 
   dia-sound c₂ s' v₂ v₃ dia-c₂ (dia-ceval=>⊆ dia-c₁ v⊆s (≡=>≈ eq-ceval-c₁)) h-err
  dia-sound (seq c₁ c₂) s v₁ v₃ dia v⊆s h-err | seq .v₁ v₂ .v₃ .c₁ .c₂ dia-c₁ dia-c₂  | later x 
   with (dia-sound c₁ s v₁ v₂ dia-c₁ v⊆s) 
  ... | c₁↯⊥ rewrite eq-ceval-c₁ = dia-sound-seq-later c₁↯⊥ dia-c₂ h h-err
   where 
    h : ∀ {s'} (h : (later x) ⇓ s') -> v₂ ⊆ dom s'
    h h₁ rewrite (sym eq-ceval-c₁) = dia-ceval=>⊆ dia-c₁ v⊆s h₁ 
  dia-sound (while b c) s v v' dia v⊆s h-err with dia
  ... | while .b .v v₁ .c b⊆s dia-c 
   with (bdia-sound b s (λ x x-in-s₁ → v⊆s x (b⊆s x x-in-s₁)))
  ... | false , eq-beval rewrite eq-beval = case h-err of λ () 
  ... | true , eq-beval with (ceval c s) in eq-ceval-c
  ... | now nothing = dia-sound c s v v₁ dia-c v⊆s (≡=>≈ eq-ceval-c) 
  dia-sound (while b c) s v v' dia v⊆s h-err | while .b .v v₁ .c b⊆s dia-c 
   | true , eq-beval | now (just s') rewrite eq-beval rewrite eq-ceval-c 
   with h-err
  ... | laterₗ w↯ = 
   dia-sound (while b c) s' v v dia (⊆-trans v⊆s (ceval⇓=>⊆ c s s' (≡=>≈ eq-ceval-c))) w↯
  dia-sound (while b c) s v v' dia v⊆s h-err | while .b .v v₁ .c b⊆s dia-c 
   | true , eq-beval | later x with (dia-sound c s v v₁ dia-c v⊆s)
  ... | c↯⊥ rewrite eq-beval rewrite eq-ceval-c = dia-sound-while-later c↯⊥ dia h h-err 
   where 
    h : ∀ {s'} (h : (later x) ⇓ s') -> v ⊆ dom s'
    h {s'} h₁ rewrite (sym eq-ceval-c) = (⊆-trans v⊆s (ceval⇓=>⊆ c s s' h₁))
 
  private 
   dia-sound-while-later : ∀ {x : Thunk (Delay (Maybe Store)) ∞} {b c} {v} (l↯⊥ : (later x)↯ -> ⊥)
    (dia : Dia v (while b c) v) (l⇓s=>⊆ : ∀ {s : Store} -> ((later x) ⇓ s) -> v ⊆ dom s)
    (w↯ : (bind (later x) (λ s -> later (ceval-while c b s))) ↯) -> ⊥
   dia-sound-while-later {x} {b} {c} {v} l↯⊥ dia l⇓s=>⊆ w↯ with (force x) in eq-force-x
   ... | now nothing = l↯⊥ (laterₗ (≡=>≈ eq-force-x)) 
   dia-sound-while-later {x} {b} {c} {v} l↯⊥ dia l⇓s=>⊆ w↯ | now (just s') with w↯
   ... | laterₗ w↯' rewrite eq-force-x with w↯'
   ... | laterₗ w↯'' = dia-sound (while b c) s' v v dia (l⇓s=>⊆ (laterₗ (≡=>≈ eq-force-x))) w↯''
   dia-sound-while-later {x} {b} {c} {v} l↯⊥ dia l⇓s=>⊆ w↯ | later x₁ with w↯
   ... | laterₗ w↯' rewrite eq-force-x with w↯'
   ... | laterₗ w↯'' = dia-sound-while-force {x₁} fx↯=>⊥ dia fx⇓=>⊆ w↯''
    where 
     lx↯=>⊥ : (hl : (later x₁) ↯) -> ⊥
     lx↯=>⊥ hl rewrite (sym eq-force-x) = l↯⊥ (laterₗ hl)
     fx↯=>⊥ : (h : (force x₁) ↯) -> ⊥
     fx↯=>⊥ h = lx↯=>⊥ (laterₗ {xs = x₁} h)
     lx⇓=>⊆ : ∀ {s : Store} → (lx₁⇓s : later x₁ ⇓ s) → v ⊆ dom s
     lx⇓=>⊆ lx₁⇓s rewrite (sym eq-force-x) =  l⇓s=>⊆ (laterₗ lx₁⇓s) 
     fx⇓=>⊆ : ∀ {s : Store} → (fx₁⇓s : force x₁ ⇓ s) → v ⊆ dom s
     fx⇓=>⊆ fx₁⇓s = lx⇓=>⊆ (laterₗ {xs = x₁} fx₁⇓s)
 
   dia-sound-while-force : ∀ {x : Thunk (Delay (Maybe Store)) ∞} {b c} {v} (l↯⊥ : (force x)↯ -> ⊥)
    (dia : Dia v (while b c) v) (l⇓s=>⊆ : ∀ {s : Store} -> ((force x) ⇓ s) -> v ⊆ dom s)
    (w↯ : (bind (force x) (λ s -> later (ceval-while c b s))) ↯) -> ⊥
   dia-sound-while-force {x} {b} {c} {v} l↯⊥ dia l⇓s=>⊆ w↯ with (force x) in eq-force-x
   ... | now nothing = l↯⊥ nown
   dia-sound-while-force {x} {b} {c} {v} l↯⊥ dia l⇓s=>⊆ w↯ | now (just s') 
    rewrite eq-force-x with w↯
   ... | laterₗ w↯' = dia-sound (while b c) s' v v dia (l⇓s=>⊆ (nowj refl)) w↯'
   dia-sound-while-force {x} {b} {c} {v} l↯⊥ dia l⇓s=>⊆ w↯ | later x₁ = dia-sound-while-later {x₁} l↯⊥ dia l⇓s=>⊆ w↯
 
 
 
   dia-sound-seq-later : ∀ {x : Thunk (Delay (Maybe Store)) ∞} {c} {v₁ v₂ : VarsSet} (l↯⊥ : (later x)↯ -> ⊥) 
    (dia : Dia v₁ c v₂) (l⇓s=>⊆ : ∀ {s : Store} -> ((later x) ⇓ s) -> v₁ ⊆ dom s ) 
    (s↯ : (bind (later x) (ceval c)) ↯) -> ⊥
   dia-sound-seq-later {x} l↯⊥ dia l⇓s=>⊆ s↯ with (force x) in eq-force-x
   ... | now nothing = l↯⊥ (laterₗ (≡=>≈ eq-force-x)) 
   dia-sound-seq-later {x} {c} {v₁} {v₂} l↯⊥ dia l⇓s=>⊆ s↯ | now (just s') with s↯
   ... | laterₗ s↯' rewrite eq-force-x = dia-sound c s' v₁ v₂ dia (l⇓s=>⊆ (laterₗ (≡=>≈ eq-force-x))) s↯'
   dia-sound-seq-later {x} {c} {v₁} {v₂} l↯⊥ dia l⇓s=>⊆ s↯ | later x₁ with s↯
   ... | laterₗ s↯' rewrite eq-force-x with s↯'
   ... | laterₗ s↯'' = dia-sound-seq-force {x₁} fx↯=>⊥ dia fx⇓=>⊆ s↯''
    where 
     lx↯=>⊥ : (hl : (later x₁) ↯) -> ⊥
     lx↯=>⊥ hl rewrite (sym eq-force-x) = l↯⊥ (laterₗ hl)
     fx↯=>⊥ : (h : (force x₁) ↯) -> ⊥
     fx↯=>⊥ h = lx↯=>⊥ (laterₗ {xs = x₁} h)
     lx⇓=>⊆ : ∀ {s : Store} → (lx₁⇓s : later x₁ ⇓ s) → v₁ ⊆ dom s
     lx⇓=>⊆ lx₁⇓s rewrite (sym eq-force-x) =  l⇓s=>⊆ (laterₗ lx₁⇓s) 
     fx⇓=>⊆ : ∀ {s : Store} → (fx₁⇓s : force x₁ ⇓ s) → v₁ ⊆ dom s
     fx⇓=>⊆ fx₁⇓s = lx⇓=>⊆ (laterₗ {xs = x₁} fx₁⇓s)
 
   dia-sound-seq-force : ∀ {x : Thunk (Delay (Maybe Store)) ∞} {c} {v₁ v₂ : VarsSet} (l↯⊥ : (force x)↯ -> ⊥) 
    (dia : Dia v₁ c v₂) (f⇓s=>⊆ : ∀ {s : Store} -> ((force x) ⇓ s) -> v₁ ⊆ dom s ) 
    (s↯ : (bind (force x) (ceval c)) ↯) -> ⊥
   dia-sound-seq-force {x} {c} {v₁} {v₂} l↯⊥ dia f⇓s=>⊆ s↯ with (force x) in eq-force-x
   ... | now (just s') rewrite eq-force-x = dia-sound c s' v₁ v₂ dia (f⇓s=>⊆ (nowj refl)) s↯
   dia-sound-seq-force {x} l↯⊥ dia f⇓s=>⊆ s↯ | now nothing rewrite eq-force-x = l↯⊥ nown
   dia-sound-seq-force {x} l↯⊥ dia f⇓s=>⊆ s↯ | later x₁ = dia-sound-seq-later {x₁} l↯⊥ dia f⇓s=>⊆ s↯
