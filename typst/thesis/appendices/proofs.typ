#import "/includes.typ": *
//typstfmt::off
= Proofs<appendix-proofs>
In this appendix we will show the Agda code for all the theorems mentioned in
the thesis.
== The partiality monad 
=== Bisimilarity

#thmref(<thm-strong-bisimilarity-equivalence>)[Theorem]
#proof[
```hs 
 reflexive : Reflexive R → ∀ {i} → Reflexive (Bisim R i)
 reflexive refl^R {i} {now r}    = now refl^R
 reflexive refl^R {i} {later rs} = later λ where .force → reflexive refl^R

 symmetric : Sym P Q → ∀ {i} → Sym (Bisim P i) (Bisim Q i)
 symmetric sym^PQ (now p)    = now (sym^PQ p)
 symmetric sym^PQ (later ps) = later λ where .force → symmetric sym^PQ (ps .force)

 transitive : Trans P Q R → ∀ {i} → Trans (Bisim P i) (Bisim Q i) (Bisim R i)
 transitive trans^PQR (now p)    (now q)    = now (trans^PQR p q)
 transitive trans^PQR (later ps) (later qs) =
   later λ where .force → transitive trans^PQR (ps .force) (qs .force)
```
]

#thmref(<thm-weak-bisimilarity-equivalence>)[Theorem]
#proof[
```hs 
 reflexive : Reflexive R -> ∀ {i} -> Reflexive (WeakBisim R i)
 reflexive refl^R {i} {now x} = now refl^R
 reflexive refl^R {i} {later x} = later λ where .force -> reflexive (refl^R) 

 symmetric : Sym P Q -> ∀ {i} -> Sym (WeakBisim P i) (WeakBisim Q i)
 symmetric sym^PQ (now x) = now (sym^PQ x)
 symmetric sym^PQ (later x) = later λ where .force -> symmetric (sym^PQ) (force x)
 symmetric sym^PQ {i} (laterₗ x ) = laterᵣ (symmetric sym^PQ x)
 symmetric sym^PQ (laterᵣ x) = laterₗ (symmetric sym^PQ x)
```
]
#thmref(<thm-delay-monad>)[Theorem]
#proof[
```hs
 left-identity : ∀ {i} (x : A) (f : A -> Delay B i) -> (now x) >>= f ≡ f x
 left-identity {i} x f = _≡_.refl

 right-identity : ∀ {i} (x : Delay A ∞) -> i ⊢ x >>= now ≈ x
 right-identity (now x) = now _≡_.refl
 right-identity {i} (later x) = later (λ where .force -> right-identity (force x))

 associativity : ∀ {i} {x : Delay A ∞} {f : A -> Delay B ∞} {g : B -> Delay C ∞} 
  -> i ⊢ (x >>= f) >>= g ≈ x >>= λ y -> (f y >>= g) 
 associativity {i} {now x} {f} {g} with (f x)
 ... | now x₁ = Codata.Sized.Delay.Bisimilarity.refl
 ... | later x₁ = Codata.Sized.Delay.Bisimilarity.refl
 associativity {i} {later x} {f} {g} = later (λ where .force -> associativity {x = force x}) 
```
]
== The Imp programming language 
=== Properties of stores 
#thmref(<imp-thm-store-inclusion-transitivity>)[Theorem]
#proof[
 ```hs
 ⊑ᵘ-trans : ∀ {s₁ s₂ s₃ : Store} (h₁ : s₁ ⊑ᵘ s₂) (h₂ : s₂ ⊑ᵘ s₃) -> s₁ ⊑ᵘ s₃
 ⊑ᵘ-trans h₁ h₂ id∈σ = h₂ (h₁ id∈σ) 
 ```
]
=== Semantics 
#thmref(<ceval-store-inclusion>)[Theorem]
#proof[
```hs
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
```
]
//typstfmt::on
