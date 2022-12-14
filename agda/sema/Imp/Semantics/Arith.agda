------------------------------------------------------------------------
-- Functional semantics for arithmetic expressions in IMP 
------------------------------------------------------------------------
module Imp.Semantics.Arith where 

open import Data.Unit
open import Imp.Syntax
open import Data.Integer 
open import Data.Bool hiding (_≟_)
open import Data.Maybe renaming (_>>=_ to _>>=m_)
open import Data.Integer.Properties as ℤ-Properties
open import Data.Nat using () renaming (suc to ℕ-suc)
--

private 
 isNonZero : ∀ (n : ℤ) -> Maybe (NonZero n)
 isNonZero (ℤ.pos (ℕ-suc n)) = just (record { nonZero = tt}) 
 isNonZero (ℤ.negsuc (ℕ-suc n)) = just (record { nonZero = tt}) 
 isNonZero _ = nothing 

aeval : ∀ (a : AExp) (s : Store) -> Maybe ℤ
aeval (const x) s = just x
aeval (var x) s = s x
aeval (plus a a₁) s = (aeval a s) >>=m (λ v₁ -> (aeval a₁ s) >>=m λ v₂ -> just (v₁ + v₂))
aeval (minus a a₁) s = (aeval a s) >>=m (λ v₁ -> (aeval a₁ s) >>=m λ v₂ -> just (v₁ - v₂))
aeval (times a a₁) s = (aeval a s) >>=m (λ v₁ -> (aeval a₁ s) >>=m λ v₂ -> just (v₁ * v₂))
aeval (div a a₁) s = 
 (aeval a s) >>=m 
  (λ v₁ -> 
   (aeval a₁ s) >>=m 
    (λ v₂ -> isNonZero v₂ >>=m 
     (λ nz -> just (_/_ v₁ v₂ {{nz}}))))

------------------------------------------------------------------------
-- Lemmas and examples 
------------------------------------------------------------------------

module _ where 

 open import Relation.Binary.PropositionalEquality
 open import Data.Or
 open ≡-Reasoning 

 mutual 
  aeval-free : ∀ s₁ s₂ a -> s₁ ≈ s₂ ⟨ a ⟩ -> (aeval a s₁) ≡ (aeval a s₂)
  aeval-free s₁ s₂ .(var i) (≈-var i sameId) = sameId
  aeval-free s₁ s₂ .(plus a₁ a₂) (≈-plus a₁ a₂ x₁ x₂) = aeval-free-comb s₁ s₂ a₁ a₂ x₁ x₂ _+_
  aeval-free s₁ s₂ .(minus a₁ a₂) (≈-minus a₁ a₂ x₁ x₂) = aeval-free-comb s₁ s₂ a₁ a₂ x₁ x₂ _-_
  aeval-free s₁ s₂ .(times a₁ a₂) (≈-times a₁ a₂ x₁ x₂) = aeval-free-comb s₁ s₂ a₁ a₂ x₁ x₂ _*_
  aeval-free s₁ s₂ .(div a₁ a₂) (≈-div a₁ a₂ x x₁) = let 
    a₁₁≡a₁₂ = aeval-free s₁ s₂ a₁ x
    a₂₁≡a₂₂ = aeval-free s₁ s₂ a₂ x₁
   in begin  
    ((aeval a₁ s₁) >>=m 
     (λ v₁ -> 
      (aeval a₂ s₁) >>=m 
       (λ v₂ -> isNonZero v₂ >>=m 
        (λ nz -> just (_/_ v₁ v₂ {{nz}})))))
    ≡⟨ cong (_>>=m 
             (λ v₁ -> 
              (aeval a₂ s₁) >>=m 
               (λ v₂ -> isNonZero v₂ >>=m 
                (λ nz -> just (_/_ v₁ v₂ {{nz}}))))) a₁₁≡a₁₂ ⟩ 
    ((aeval a₁ s₂) >>=m 
     (λ v₁ -> 
      (aeval a₂ s₁) >>=m 
       (λ v₂ -> isNonZero v₂ >>=m 
        (λ nz -> just (_/_ v₁ v₂ {{nz}})))))
    ≡⟨ cong (λ v -> 
             ((aeval a₁ s₂) >>=m 
              (λ v₁ -> v >>=m 
               (λ v₂ -> isNonZero v₂ >>=m 
                (λ nz -> just (_/_ v₁ v₂ {{nz}})))))) a₂₁≡a₂₂ ⟩ 
    ((aeval a₁ s₂) >>=m 
     (λ v₁ -> 
      (aeval a₂ s₂) >>=m 
       (λ v₂ -> isNonZero v₂ >>=m 
        (λ nz -> just (_/_ v₁ v₂ {{nz}})))))
    ∎

  aeval-free-comb : ∀ s₁ s₂ a₁ a₂ -> s₁ ≈ s₂ ⟨ a₁ ⟩ -> s₁ ≈ s₂ ⟨ a₂ ⟩ -> (f : ℤ -> ℤ -> ℤ) -> 
     (aeval a₁ s₁ >>=m 
      (λ z → aeval a₂ s₁ >>=m 
       (λ z₁ → just (f z z₁)))) 
       ≡ (aeval a₁ s₂ >>=m 
          (λ z → aeval a₂ s₂ >>=m 
           (λ z₁ → just (f z z₁)))) 
  aeval-free-comb s₁ s₂ a₁ a₂ x x₁ f = 
   let 
    a₁₁≡a₁₂ = aeval-free s₁ s₂ a₁ x
    a₂₁≡a₂₂ = aeval-free s₁ s₂ a₂ x₁
   in begin 
     (aeval a₁ s₁ >>=m (λ z → aeval a₂ s₁ >>=m (λ z₁ → just (f z z₁)))) 
    ≡⟨ cong (_>>=m λ z → aeval a₂ s₁ >>=m (λ z₁ → just (f z z₁))) a₁₁≡a₁₂ ⟩ 
     (aeval a₁ s₂ >>=m (λ z → aeval a₂ s₁ >>=m (λ z₁ → just (f z z₁)))) 
    ≡⟨ cong (λ v -> (aeval a₁ s₂ >>=m (λ z → v >>=m (λ z₁ → just (f z z₁))))) a₂₁≡a₂₂ ⟩
     (aeval a₁ s₂ >>=m (λ z → aeval a₂ s₂ >>=m (λ z₁ → just (f z z₁)))) ∎
