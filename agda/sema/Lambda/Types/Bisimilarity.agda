----------------------------------------------------------------------------------------------
-- Bisimilarity for the types of the λ calculus with constants
----------------------------------------------------------------------------------------------
module Lambda.Types.Bisimilarity where 

open import Size 
open import Relation.Binary
open import Lambda.Types.Core
open import Codata.Sized.Thunk
--

data Bisim (i : Size) : Ty ∞ -> Ty ∞ -> Set where 
  ≈-⋆ : Bisim i (⋆) (⋆)
  ≈-=> : ∀ {t1 t2 t3 t4} -> Thunk^R Bisim i t1 t3 -> 
             Thunk^R Bisim i t2 t4 -> Bisim i (t1 => t2) (t3 => t4)

reflexive : ∀ {i} → Reflexive (Bisim i)
reflexive {i} {⋆} = ≈-⋆
reflexive {i} {x => x₁} = ≈-=> (λ where .force -> reflexive) (λ where .force -> reflexive)
