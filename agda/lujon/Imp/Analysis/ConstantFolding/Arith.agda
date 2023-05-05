------------------------------------------------------------------------
-- Constant folding for arithmetic expressions of Imp
------------------------------------------------------------------------
module Imp.Analysis.ConstantFolding.Arith where

open import Data.Unit
open import Data.Maybe
open import Data.Integer
open import Imp.Syntax.Ident
open import Imp.Syntax.Arith
open import Data.Integer.Properties as ℤ-Properties
open import Data.Nat using () renaming (suc to ℕ-suc)
---

private 
 isNonZero : ∀ (n : ℤ) -> Maybe (NonZero n)
 isNonZero (ℤ.pos (ℕ-suc n)) = just (record { nonZero = tt}) 
 isNonZero (ℤ.negsuc (ℕ-suc n)) = just (record { nonZero = tt}) 
 isNonZero _ = nothing 

 case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
 case x of f = f x


afold : (a : AExp) -> (s : Store) -> AExp
afold (const x) _ = const x 
afold (var id) s with (s id)  
... | just v = const v
... | nothing = var id
afold (plus a₁ a₂) s with (afold a₁ s) | (afold a₂ s)
... | const v₁ | const v₂ = const (v₁ + v₂)
... | a₁' | a₂' = plus a₁' a₂'
afold (minus a₁ a₂) s with (afold a₁ s) | (afold a₂ s)
... | const v₁ | const v₂ = const (v₁ - v₂)
... | a₁' | a₂' = minus a₁' a₂'
afold (times a₁ a₂) s with (afold a₁ s) | (afold a₂ s)
... | const v₁ | const v₂ = const (v₁ * v₂)
... | a₁' | a₂' = times a₁' a₂'
afold (div a₁ a₂) s with (afold a₁ s) | (afold a₂ s)
... | const v₁ | const v₂ = case (isNonZero v₂) of λ { 
  (just t) -> const (_/_ v₁ v₂ {{t}}) ; 
  nothing -> (div a₁ a₂) }
... | a₁' | a₂' = div a₁' a₂'


------------------------------------------------------------------------
-- Properties of constant folding 
------------------------------------------------------------------------
module _ where
 open import Data.Or
 open import Data.Empty
 open import Data.Product
 open import Imp.Syntax.Properties
 open import Relation.Nullary.Negation
 open import Imp.Semantics.Functional.Arith
 open import Relation.Binary.PropositionalEquality 
 open import Relation.Binary.PropositionalEquality.Core
 open ≡-Reasoning

 -- If a `var id` folds to a `var id₁`, it means that its value wasn't in the store.
 afold-var-nothing : ∀ {s id id₁} (h : afold (var id) s ≡ (var id₁)) -> s id ≡ nothing
 afold-var-nothing {s} {id} {id₁} h with (s id) 
 ... | nothing = refl

 afold-nothing-var : ∀ {s id} (h : s id ≡ nothing) -> (afold (var id) s ≡  var id)
 afold-nothing-var {s} {id} h with (s id) 
 ... | nothing = refl 

 -- If a `var id` folds to a `var id₁`, it means that `id ≡ id₁`. 
 afold-var-same-id : ∀ {s id id₁} (h : afold (var id) s ≡ (var id₁)) -> id ≡ id₁
 afold-var-same-id {s} {id} {id₁} h with (s id) in eq-id
 ... | nothing rewrite eq-id = eq-var-id h 

 -- If a `var id` folds to a `const v`, it means that its value was in the store.
 afold-var-const : ∀ {s id v} (h : afold (var id) s ≡ const v) -> s id ≡ just v
 afold-var-const {s} {id} {v} h with (s id) in eq-id
 ... | just x rewrite eq-id =
  let 
   x≡v = eq-const-v h
  in 
   begin 
    just x
   ≡⟨ cong just x≡v ⟩ 
    just v
   ∎

 -- Plus (and other binary operators) behave compositionally if any of the two operands don't fold to constants.
 postulate
  afold-plus-notconst : ∀ {s a₁ a₂ v₁ v₂} 
   (h : Or (afold a₁ s ≢ const v₁) (afold a₂ s ≢ const v₂)) 
    -> (afold (plus a₁ a₂) s ≡ plus (afold a₁ s) (afold a₂ s) )

 -- Folding is idempotent under the same store. 
 afold-idem : ∀ a {s} -> afold a s ≡ afold (afold a s) s
 afold-idem (const n) = refl
 afold-idem (var id) {s} with (s id) in eq-id
 ... | just x = refl
 ... | nothing rewrite eq-id = refl
 afold-idem (plus a₁ a₂) {s} with (afold a₁ s) in eq-afold-a₁ | (afold a₂ s) in eq-afold-a₂
 ... | const n | const n₁ = refl
 ... | const n | var id = 
  let 
   plus-comp = afold-plus-notconst {s} {a₁} {a₂} (right λ x -> ? )
  in ?  
 ... | const n | plus a₂' a₂'' = {! !}
 ... | const n | minus a₂' a₂'' = {! !}
 ... | const n | times a₂' a₂'' = {! !}
 ... | const n | div a₂' a₂'' = {! !}
 ... | var id | a₂' = {! !}
 ... | plus a₁' a₁'' | a₂' = {! !}
 ... | minus a₁' a₁'' | a₂' = {! !}
 ... | times a₁' a₁'' | a₂' = {! !}
 ... | div a₁' a₁'' | a₂' = {! !}







--
-- ... | const n | var id = 
--  let 
--   s-id-is-nothing = afold-var-nothing {s} {id} {id} 
--    (begin 
--      afold (var id) s 
--     ≡⟨ cong (λ a -> afold a s) (sym (afold-var-var {a₂} {id} {s} eq-afold-a₂)) ⟩ 
--      afold a₂ s 
--     ≡⟨ eq-afold-a₂ ⟩ 
--      var id 
--     ∎)
--  in 
--   sym(
--   begin 
--    afold (plus (const n) (var id)) s
--   ≡⟨ afold-plus-notconst {s} {const n} {var id} (right (let )) ⟩ 
--    plus (afold (const n) s) (afold (var id) s)
--   ≡⟨ ? ⟩ 
--    plus (const n) (afold (var id) s) 
--   ≡⟨ cong (λ v -> plus (const n) v) (afold-nothing-var {s} {id} s-id-is-nothing) ⟩ 
--    plus (const n) (var id) 
--   ∎)
-- ... | const n | plus a₂' a₂'' = {! !}
-- ... | const n | minus a₂' a₂'' = {! !}
-- ... | const n | times a₂' a₂'' = {! !}
-- ... | const n | div a₂' a₂'' = {! !}
-- ... | var id | a₂' = {! !}
-- ... | plus a₁' a₁'' | a₂' = {! !}
-- ... | minus a₁' a₁'' | a₂' = {! !}
-- ... | times a₁' a₁'' | a₂' = {! !}
-- ... | div a₁' a₁'' | a₂' = {! !}
 afold-idem (minus a₁ a₂) = {! !}
 afold-idem (times a₁ a₂) = {! !}
 afold-idem (div a₁ a₂) = {! !}
--
--
-- -- Folding preserves semantics.
-- afold-sound : ∀ a {s t : Store} {p : t ≅ s} -> (aeval a s ≡ aeval (afold a t) s)
-- afold-sound = ?
