module Lambda.Semantics.Properties where

open import Size
open import Data.Vec
open import Data.Maybe hiding (_>>=_)
open import Lambda.Syntax
open import Relation.Binary
open import Codata.Sized.Thunk
open import Lambda.Syntax.Term
open import Lambda.Syntax.Value
open import Lambda.Semantics.Core
open import Codata.Sized.Delay hiding (never)
import Codata.Sized.Partial.Bisimilarity.Core
open import Codata.Sized.Partial using (never)
open import Codata.Sized.Partial.Bisimilarity
open import Codata.Sized.Partial.Effectful renaming (bind to _>>=_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
---

-- Ω is weakly bisimilar to never.
Ω-loops : ∀ {i} -> i ⊢ (eval Ω []) ≈ never
Ω-loops = later (λ where .force -> Ω-loops) 

infix 5 _⟦∙⟧_

_⟦∙⟧_ : Delay (Maybe Value) ∞ → Delay (Maybe Value) ∞ → Delay (Maybe Value) ∞
mv₁ ⟦∙⟧ mv₂ = mv₁ >>= (λ f -> mv₂ >>= λ v -> apply f v)

∙-comp : ∀ {n} (t₁ t₂ : Tm n) {ρ} → (i : Size) ->
         (eval (t-app t₁ t₂) ρ) ≡ ((eval t₁ ρ)  ⟦∙⟧  (eval t₂ ρ))
∙-comp {n} t₁ t₂ {ρ} i = refl
