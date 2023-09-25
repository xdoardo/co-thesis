#import "/includes.typ": *
//typstfmt::off
= Proofs<appendix-proofs>
In this appendix we will show the Agda code for all the theorems mentioned in
the thesis.
== The delay monad 

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
<proof-weak-bisimilarity-equivalence>
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
<proof-delay-monad>
]


== The Imp programming language 
#thmref(<imp-thm-store-tilde-transitive>)[Theorem]
#proof[
 #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L87")[
 ```
 ∻-trans : ∀ {s₁ s₂ s₃ : Store} (h₁ : s₁ ∻ s₂) (h₂ : s₂ ∻ s₃) -> s₁ ∻ s₃
 ∻-trans h₁ h₂ id∈σ = h₂ (h₁ id∈σ) 
 ```
 ]
 <proof-tilde-transitive>
]
#block(breakable: false)[
#thmref(<lemma-ceval-store-tilde>)[Theorem]
#proof[
  #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Semantics/BigStep/Functional/Properties.agda#L91")[
```hs
ceval⇓=>⊑ᵘ : ∀ (c : Command) (s s' : Store) (h⇓ : (ceval c s) ⇓ s') 
              -> s ⊑ᵘ s'
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
... | c₂⇓s' = 
  ⊑ᵘ-trans (ceval⇓=>⊑ᵘ c₁ s sⁱ c₁⇓sⁱ {id}) 
    (ceval⇓=>⊑ᵘ c₂ sⁱ s' c₂⇓s' {id}) {id}
ceval⇓=>⊑ᵘ (while b c) s s' h⇓ {id} x 
 with (beval b s) in eq-b
... | just false with h⇓
... | nowj refl = x
ceval⇓=>⊑ᵘ (while b c) s s' h⇓ {id} x
 | just true rewrite eq-b = 
  while-⊑ᵘ c b s s' (λ s₁ s₂ h -> ceval⇓=>⊑ᵘ c s₁ s₂ h) h⇓ {id} x
```
]
<proof-ceval-store-tilde>
]]


#block(breakable: false)[
#thmref(<thm-cf-equiv>)[Theorem]
#proof[
  #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Data/CharacteristicFunction.agda#L49")[
    ```hs
 cf-ext : ∀ {s₁ s₂ : CharacteristicFunction} -> (a-ex : ∀ x -> s₁ x ≡ s₂ x) -> s₁ ≡ s₂
 cf-ext a-ex = ext a Agda.Primitive.lzero a-ex
 ```
    ]
    <proof-cf-equiv>
  ]
]
#block(breakable: false)[
  #thmref(<lemma-ceval-sc-subeq>)[Lemma]
  #proof[
    #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Semantics/BigStep/Functional/Properties.agda#L134")[
```hs
ceval⇓=>sc⊆s' :  ∀ (c : Command) (s s' : Store) (h⇓ : (ceval c s) ⇓ s') -> (dom s ∪ (cvars c)) ⊆ (dom s')
ceval⇓=>sc⊆s' skip s .s (now refl) x x-in-s₁ rewrite (cvars-skip) rewrite (∨-identityʳ (dom s x)) = x-in-s₁
ceval⇓=>sc⊆s' (assign id a) s s' h⇓ x x-in-s₁ with (aeval a s)
... | nothing with h⇓
... | now ()
ceval⇓=>sc⊆s' (assign id a) s s' h⇓ x x-in-s₁ | just v with h⇓
... | now refl
 with (id == x) in eq-id
... | true = refl
... | false rewrite eq-id rewrite (∨-identityʳ (dom s x)) with s x in eq-sx
... | just x₁ rewrite eq-sx = refl
ceval⇓=>sc⊆s' (ifelse b cᵗ cᶠ) s s' h⇓ x x-in-s₁ with (beval b s) in eq-b 
... | nothing with h⇓
... | now ()
ceval⇓=>sc⊆s' (ifelse b cᵗ cᶠ) s s' h⇓ x x-in-s₁ | just false rewrite eq-b 
 = ceval⇓=>sc⊆s' cᶠ s s' h⇓ x (h {dom s x} {cvars cᵗ x} {cvars cᶠ x} x-in-s₁)
ceval⇓=>sc⊆s' (ifelse b cᵗ cᶠ) s s' h⇓ x x-in-s₁ | just true rewrite eq-b 
 = ceval⇓=>sc⊆s' cᵗ s s' h⇓ x (h {dom s x} {cvars cᵗ x} {cvars cᶠ x}  x-in-s₁)
ceval⇓=>sc⊆s' (seq c₁ c₂) s s' h⇓ x x-in-s₁
 with (bindxf⇓=>x⇓ {x = ceval c₁ s} {f = ceval c₂} h⇓)
... | sⁱ , c₁⇓sⁱ with (bindxf⇓-x⇓=>f⇓ {x = ceval c₁ s} {f = ceval c₂} h⇓ c₁⇓sⁱ)
... | c₂⇓s' with (ceval⇓=>sc⊆s' c₁ s sⁱ c₁⇓sⁱ x)
... | n with (ceval⇓=>sc⊆s' c₂ sⁱ s' c₂⇓s' x)
... | n' with (dom s x) | (cvars c₁ x) | (cvars c₂ x)
... | false | false | true rewrite (∨-zeroʳ (dom sⁱ x)) = n' refl 
... | false | true | false rewrite (∨-zeroˡ (false)) rewrite (∨-identityʳ (dom sⁱ x)) = n' (n refl)
... | false | true | true rewrite (∨-zeroˡ (false)) rewrite (∨-zeroʳ (dom sⁱ x)) = n' refl
... | true | n2 | n3 rewrite (∨-zeroˡ (true)) rewrite (n refl) rewrite (∨-identityʳ (dom sⁱ x)) 
 = n' refl
ceval⇓=>sc⊆s' (while b c) s s' h⇓ x x-in-s₁ rewrite (cvars-while {b} {c}) 
 rewrite (∨-identityʳ (dom s x)) = ceval⇓=>⊆ (while b c) s s' h⇓ x x-in-s₁ 
```
      ]
    ]
    <proof-ceval-sc-subeq>
  ]
#block(breakable: false)[
  #thmref(<thm-adia-sound>)[Theorem]
  #proof[
    #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L48")[
      ```hs
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
      ```
      ]
      <proof-adia-sound>
    ]
  ]
#block(breakable: false)[
  #thmref(<thm-bdia-sound>)[Theorem]
  #proof[
    #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L60")[
      ```hs
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
      ```
      ]
      <proof-bdia-sound>
    ]
  ]
#block(breakable: false)[
  #thmref(<thm-dia-sound>)[Theorem]
  #proof[
    #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L117")[
      ```hs
  dia-sound : ∀ (c : Command) (s : Store) (v v' : VarsSet) (dia : Dia v c v') (v⊆s : v ⊆ dom s) -> (h-err : (ceval c s) ↯) -> ⊥
  dia-sound skip s v v' dia v⊆s (now ())
  dia-sound (assign id a) s v .(id ↦ v) (assign .a .v .id a⊆v) v⊆s h-err with (adia-sound a s (⊆-trans a⊆v v⊆s)) ... | a' , eq-aeval with h-err
  ... | now ()
  dia-sound (ifelse b cᵗ cᶠ) s v .(vᵗ ∩ vᶠ) (if .b .v vᵗ vᶠ .cᵗ .cᶠ b⊆v diaᶠ diaᵗ) v⊆s h-err with (bdia-sound b s λ x x-in-s₁ → v⊆s x (b⊆v x x-in-s₁))
  ... | false , eq-beval rewrite eq-beval rewrite eq-beval = dia-sound cᶠ s v vᶠ diaᶠ v⊆s h-err
  dia-sound (ifelse b cᵗ cᶠ) s v .(vᵗ ∩ vᶠ) (if .b .v vᵗ vᶠ .cᵗ .cᶠ b⊆v diaᶠ diaᵗ) v⊆s h-err | true , eq-beval rewrite eq-beval rewrite eq-beval = dia-sound cᵗ s v vᵗ diaᵗ v⊆s h-err
  dia-sound (seq c₁ c₂) s v₁ v₃ dia v⊆s h-err with dia
  ... | seq .v₁ v₂ .v₃ .c₁ .c₂ dia-c₁ dia-c₂ with (ceval c₁ s) in eq-ceval-c₁
  ... | now nothing = dia-sound c₁ s v₁ v₂ dia-c₁ v⊆s (≡=>≋ eq-ceval-c₁) 
  ... | now (just s') rewrite eq-ceval-c₁ = dia-sound c₂ s' v₂ v₃ dia-c₂ (dia-ceval=>⊆ dia-c₁ v⊆s (≡=>≋ eq-ceval-c₁)) h-err
  dia-sound (seq c₁ c₂) s v₁ v₃ dia v⊆s h-err | seq .v₁ v₂ .v₃ .c₁ .c₂ dia-c₁ dia-c₂  | later x with (dia-sound c₁ s v₁ v₂ dia-c₁ v⊆s) 
  ... | c₁↯⊥ rewrite eq-ceval-c₁ = dia-sound-seq-later c₁↯⊥ dia-c₂ h h-err
  dia-sound (while b c) s v v' dia v⊆s h-err with dia
  ... | while .b .v v₁ .c b⊆s dia-c with (bdia-sound b s (λ x x-in-s₁ → v⊆s x (b⊆s x x-in-s₁)))
  ... | false , eq-beval rewrite eq-beval with h-err
  ... | now ()
  dia-sound (while b c) s v v' dia v⊆s h-err | while .b .v v₁ .c b⊆s dia-c | true , eq-beval with (ceval c s) in eq-ceval-c
  ... | now nothing = dia-sound c s v v₁ dia-c v⊆s (≡=>≋ eq-ceval-c) 
  dia-sound (while b c) s v v' dia v⊆s h-err | while .b .v v₁ .c b⊆s dia-c | true , eq-beval | now (just s') rewrite eq-beval rewrite eq-ceval-c with h-err
  ... | laterₗ w↯ = dia-sound (while b c) s' v v dia (⊆-trans v⊆s (ceval⇓=>⊆ c s s' (≡=>≋ eq-ceval-c))) w↯
  dia-sound (while b c) s v v' dia v⊆s h-err | while .b .v v₁ .c b⊆s dia-c | true , eq-beval | later x with (dia-sound c s v v₁ dia-c v⊆s)
  ... | c↯⊥ rewrite eq-beval rewrite eq-ceval-c = dia-sound-while-later c↯⊥ dia h h-err 
      ```
      ]
      <proof-dia-sound>
    ]
  ]
#block(breakable: false)[
  #thmref(<thm-apfold-sound>)[Theorem]
  #proof[
    #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/PureFolding/Arith.agda#L31")[
      ```hs
 -- Pure constant folding preserves semantics.
 apfold-sound : ∀ a s -> (aeval a s ≡ aeval (apfold a) s)
 apfold-sound (const n) _ = refl
 apfold-sound (var id) _ = refl
 apfold-sound (plus a₁ a₂) s 
  rewrite (apfold-sound a₁ s) 
  rewrite (apfold-sound a₂ s)  
  with (apfold a₁) in eq-a₁ | (apfold a₂) in eq-a₂
 ... | const n | const n₁  = refl
 ... | const n | var id     = refl
 ... | const n | plus v₂ v₃ = refl
 ... | var id     | v₂ = refl
 ... | plus v₁ v₃ | v₂ = refl
      ```
      ]
<proof-apfold-sound>
    ]]

#block(breakable: false)[
  #thmref(<thm-bpfold-sound>)[Theorem]
  #proof[
    #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/PureFolding/Bool.agda#L38")[
      ```hs
 bpfold-sound : ∀ b s  -> (beval b s ≡ beval (bpfold b) s)
 bpfold-sound (const b) s  = refl
 bpfold-sound (le a₁ a₂) s rewrite (apfold-sound a₁ s) rewrite (apfold-sound a₂ s) 
  with (apfold a₁) | (apfold a₂)
 ... | const n | const n₁ = refl
 ... | const n | var id = refl
 ... | const n | plus v₂ v₃ = refl
 ... | var id | v₂ = refl
 ... | plus v₁ v₃ | v₂ = refl
 bpfold-sound (not b) s rewrite (bpfold-sound b s) with (bpfold b) 
 ... | const b₁ = refl
 ... | le a₁ a₂ = refl
 ... | not v = refl
 ... | and v v₁ = refl
 bpfold-sound (and b₁ b₂) s rewrite (bpfold-sound b₁ s) rewrite (bpfold-sound b₂ s) 
  with (bpfold b₁) | (bpfold b₂) 
 ... | const b | const b₃ = refl
 ... | const b | le a₁ a₂ = refl
 ... | const b | not v₂ = refl
 ... | const b | and v₂ v₃ = refl
 ... | le a₁ a₂ | v₂ = refl
 ... | not v₁ | v₂ = refl
 ... | and v₁ v₃ | v₂ = refl
      ```
      ]
<proof-bpfold-sound>
    ]]

#block(breakable: false)[
  #thmref(<thm-cpfold-sound>)[Theorem]
  #proof[
    #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/PureFolding/Command.agda#L50")[
      ```hs
  cpfold-sound : ∀ (c : Command) (s : Store) -> ∞ ⊢ (ceval c s) ≋ (ceval (cpfold c) s)
  cpfold-sound skip s rewrite (cpfold-skip) = now refl 
  cpfold-sound (assign id a) s = ≡=>≋ (cpfold-assign a id s)
  cpfold-sound (ifelse b cᵗ cᶠ) s = cpfold-if b cᵗ cᶠ s
  cpfold-sound (seq c₁ c₂) s = cpfold-seq c₁ c₂ s
  cpfold-sound (while b c) s = cpfold-while b c s 
  -- way to long..
      ```
      ]
<proof-cpfold-sound>
    ]]
//typstfmt::on
