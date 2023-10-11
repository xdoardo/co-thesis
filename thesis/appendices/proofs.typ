#import "/includes.typ": *

//typstfmt::off
= Proofs<appendix-proofs>
== The delay monad 
#refproof(label: <proof-weak-bisimilarity-equivalence>, thmref: <thm-weak-bisimilarity-equivalence>)[
  #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/Delay/WeakBisimilarity/Relation/Binary/Equivalence.agda#L16")[
```hs 
 reflexive : Reflexive R -> ∀ {i} -> Reflexive (WeakBisim R i)
 reflexive refl^R {i} {now x} = now refl^R
 reflexive refl^R {i} {later x} = later λ where .force -> reflexive (refl^R) 

 symmetric : Sym P Q -> ∀ {i} -> Sym (WeakBisim P i) (WeakBisim Q i)
 symmetric sym^PQ (now x) = now (sym^PQ x)
 symmetric sym^PQ (later x) = later λ where .force -> symmetric (sym^PQ) (force x)
 symmetric sym^PQ {i} (laterₗ x ) = laterᵣ (symmetric sym^PQ x)
 symmetric sym^PQ (laterᵣ x) = laterₗ (symmetric sym^PQ x)

 --- ... 
 transitive-now : ∀ {i} {x y z} (t : Trans P Q R) (p : WeakBisim P ∞ (now x) y) 
  (q : WeakBisim Q ∞ y z) -> WeakBisim R i (now x) z
 transitive-now t (now p) (now q) = now (t p q)
 transitive-now t (now p) (laterᵣ q) = laterᵣ (transitive-now t (now p) q) 
 transitive-now t (laterᵣ p) (later x) = laterᵣ (transitive-now t p (force x))
 transitive-now t (laterᵣ p) (laterᵣ q) = laterᵣ (transitive-now t p (laterˡ⁻¹ q))
 transitive-now t (laterᵣ p) (laterₗ q) = transitive-now t p q
 
 mutual 
  transitive-later : ∀ {i} {x y z} (t : Trans P Q R) (p : WeakBisim P ∞ (later x) y) 
   (q : WeakBisim Q ∞ y z) -> WeakBisim R i (later x) z
  transitive-later t p (later q)  = later λ { .force → transitive t (later⁻¹ p) (force q) }
  transitive-later t p (laterᵣ q) = later λ { .force → transitive t (laterˡ⁻¹ p) q }
  transitive-later t p (laterₗ q) = transitive-later t (laterʳ⁻¹ p) q
  transitive-later t (laterₗ p) (now q) = laterₗ (transitive t p (now q))

  transitive : ∀ {i} (t : Trans P Q R) -> Trans (WeakBisim P ∞) (WeakBisim Q ∞) (WeakBisim R i)
  transitive t {now x} p q = transitive-now t p q 
  transitive t {later x} p q = transitive-later t p q 
```
]]

#refproof(label: <proof-delay-monad>, thmref: <thm-delay-monad>)[
  #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/Delay/Examples.agda#L19")[
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
]]


== The Imp programming language 
#refproof(label: <proof-tilde-transitive>, thmref: <thm-imp-store-tilde-transitive>)[
 #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L87")[
 ```
 ∻-trans : ∀ {s₁ s₂ s₃ : Store} (h₁ : s₁ ∻ s₂) (h₂ : s₂ ∻ s₃) -> s₁ ∻ s₃
 ∻-trans h₁ h₂ id∈σ = h₂ (h₁ id∈σ) 
 ```
 ]
]
#block(breakable: false)[
#refproof(label: <proof-ceval-store-tilde>, thmref: <lemma-ceval-store-tilde>)[
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
]]
]

#block(breakable: false)[
#refproof(label: <proof-cf-equiv>, thmref:<thm-cf-equiv>)[
  #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Data/CharacteristicFunction.agda#L49")[
    ```hs
 cf-ext : ∀ {s₁ s₂ : CharacteristicFunction} -> (a-ex : ∀ x -> s₁ x ≡ s₂ x) -> s₁ ≡ s₂
 cf-ext a-ex = ext a Agda.Primitive.lzero a-ex
 ```
    ]] 
]
#block(breakable: false)[
  #refproof(label: <proof-ceval-sc-subeq>, thmref: <lemma-ceval-sc-subeq>)[
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
  ]
#block(breakable: false)[
  #refproof(label: <proof-adia-safe>, thmref: <thm-adia-safe>)[
    #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L48")[
      ```hs
 adia-safe : ∀ (a : AExp) (s : Store) -> (dia : avars a ⊆ dom s) -> (∃ λ v -> aeval a s ≡ just v)
 adia-safe (const n) s dia = n , refl
 adia-safe (var id) s dia 
  with (avars (var id) id) in eq-avars-id
 ... | false rewrite (==-refl {id}) with eq-avars-id
 ... | ()
 adia-safe (var id) s dia | true = in-dom-has-value {s} {id} (dia id eq-avars-id)
 adia-safe (plus a₁ a₂) s dia 
  with (adia-safe a₁ s (⊆-trans (⊏ᵃ=>⊆ a₁ (plus a₁ a₂) (plus-l a₁ a₂)) dia))
 ... | v₁ , eq-aev-a₁ 
  with (adia-safe a₂ s (⊆-trans (⊏ᵃ=>⊆ a₂ (plus a₁ a₂) (plus-r a₁ a₂)) dia))
 ... | v₂ , eq-aev-a₂ rewrite eq-aev-a₁ rewrite eq-aev-a₂ = v₁ + v₂ , refl
      ```
      ]
    ]
  ]
#block(breakable: false)[
  #refproof(label: <proof-bdia-safe>, thmref: <thm-bdia-safe>)[
    #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L60")[
      ```hs
 bdia-safe : ∀ (b : BExp) (s : Store) -> (dia : bvars b ⊆ dom s) -> (∃ λ v -> beval b s ≡ just v)
 bdia-safe (const b) s dia = b , refl
 bdia-safe (le a₁ a₂) s dia 
  with (adia-safe a₁ s (⊆-trans (⊏ᵇᵃ=>⊆ a₁ (le a₁ a₂) (le-l a₁ a₂)) dia)) 
   | (adia-safe a₂ s (⊆-trans (⊏ᵇᵃ=>⊆ a₂ (le a₁ a₂) (le-r a₁ a₂)) dia))
 ... | v₁ , eq-a₁ | v₂ , eq-a₂ rewrite eq-a₁ rewrite eq-a₂ = (v₁ ≤ᵇ v₂) , refl
 bdia-safe (BExp.not b) s dia 
  with (bdia-safe b s (⊆-trans (⊏ᵇᵇ=>⊆ b (BExp.not b) (_⊏ᵇ_.not b)) dia))
 ... | v , eq-b rewrite eq-b = (Data.Bool.not v) , refl
 bdia-safe (and b₁ b₂) s dia
  with (bdia-safe b₁ s (⊆-trans (⊏ᵇᵇ=>⊆ b₁ (and b₁ b₂) (and-l b₁ b₂)) dia)) 
   | (bdia-safe b₂ s (⊆-trans (⊏ᵇᵇ=>⊆ b₂ (and b₁ b₂) (and-r b₁ b₂)) dia))
 ... | v₁ , eq-b₁ | v₂ , eq-b₂ rewrite eq-b₁ rewrite eq-b₂ = (v₁ ∧ v₂) , refl
      ```
      ]
    ]
  ]
#block(breakable: false)[
  #refproof(label: <proof-dia-safe>, thmref: <thm-dia-safe>)[
    #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L117")[
      ```hs
  dia-safe : ∀ (c : Command) (s : Store) (v v' : VarsSet) (dia : Dia v c v') (v⊆s : v ⊆ dom s) -> (h-err : (ceval c s) ↯) -> ⊥
  dia-safe skip s v v' dia v⊆s (now ())
  dia-safe (assign id a) s v .(id ↦ v) (assign .a .v .id a⊆v) v⊆s h-err with (adia-safe a s (⊆-trans a⊆v v⊆s)) ... | a' , eq-aeval with h-err
  ... | now ()
  dia-safe (ifelse b cᵗ cᶠ) s v .(vᵗ ∩ vᶠ) (if .b .v vᵗ vᶠ .cᵗ .cᶠ b⊆v diaᶠ diaᵗ) v⊆s h-err with (bdia-safe b s λ x x-in-s₁ → v⊆s x (b⊆v x x-in-s₁))
  ... | false , eq-beval rewrite eq-beval rewrite eq-beval = dia-safe cᶠ s v vᶠ diaᶠ v⊆s h-err
  dia-safe (ifelse b cᵗ cᶠ) s v .(vᵗ ∩ vᶠ) (if .b .v vᵗ vᶠ .cᵗ .cᶠ b⊆v diaᶠ diaᵗ) v⊆s h-err | true , eq-beval rewrite eq-beval rewrite eq-beval = dia-safe cᵗ s v vᵗ diaᵗ v⊆s h-err
  dia-safe (seq c₁ c₂) s v₁ v₃ dia v⊆s h-err with dia
  ... | seq .v₁ v₂ .v₃ .c₁ .c₂ dia-c₁ dia-c₂ with (ceval c₁ s) in eq-ceval-c₁
  ... | now nothing = dia-safe c₁ s v₁ v₂ dia-c₁ v⊆s (≡=>≋ eq-ceval-c₁) 
  ... | now (just s') rewrite eq-ceval-c₁ = dia-safe c₂ s' v₂ v₃ dia-c₂ (dia-ceval=>⊆ dia-c₁ v⊆s (≡=>≋ eq-ceval-c₁)) h-err
  dia-safe (seq c₁ c₂) s v₁ v₃ dia v⊆s h-err | seq .v₁ v₂ .v₃ .c₁ .c₂ dia-c₁ dia-c₂  | later x with (dia-safe c₁ s v₁ v₂ dia-c₁ v⊆s) 
  ... | c₁↯⊥ rewrite eq-ceval-c₁ = dia-safe-seq-later c₁↯⊥ dia-c₂ h h-err
  dia-safe (while b c) s v v' dia v⊆s h-err with dia
  ... | while .b .v v₁ .c b⊆s dia-c with (bdia-safe b s (λ x x-in-s₁ → v⊆s x (b⊆s x x-in-s₁)))
  ... | false , eq-beval rewrite eq-beval with h-err
  ... | now ()
  dia-safe (while b c) s v v' dia v⊆s h-err | while .b .v v₁ .c b⊆s dia-c | true , eq-beval with (ceval c s) in eq-ceval-c
  ... | now nothing = dia-safe c s v v₁ dia-c v⊆s (≡=>≋ eq-ceval-c) 
  dia-safe (while b c) s v v' dia v⊆s h-err | while .b .v v₁ .c b⊆s dia-c | true , eq-beval | now (just s') rewrite eq-beval rewrite eq-ceval-c with h-err
  ... | laterₗ w↯ = dia-safe (while b c) s' v v dia (⊆-trans v⊆s (ceval⇓=>⊆ c s s' (≡=>≋ eq-ceval-c))) w↯
  dia-safe (while b c) s v v' dia v⊆s h-err | while .b .v v₁ .c b⊆s dia-c | true , eq-beval | later x with (dia-safe c s v v₁ dia-c v⊆s)
  ... | c↯⊥ rewrite eq-beval rewrite eq-ceval-c = dia-safe-while-later c↯⊥ dia h h-err 
      ```
      ]
    ]
  ]
#block(breakable: false)[
  #proof(label:<proof-dia-sound-while-later>)[
    #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L165")[
    ```hs
 dia-sound-while-later : ∀ {x : Thunk (Delay (Maybe Store)) ∞} {b c} {v} (l↯⊥ : (later x)↯ -> ⊥)
    (dia : Dia v (while b c) v) (l⇓s=>⊆ : ∀ {s : Store} -> ((later x) ⇓ s) -> v ⊆ dom s)
    (w↯ : (bind (later x) (λ s -> later (ceval-while c b s))) ↯) -> ⊥
   dia-sound-while-later {x} {b} {c} {v} l↯⊥ dia l⇓s=>⊆ w↯ with (force x) in eq-force-x
   ... | now nothing = l↯⊥ (laterₗ (≡=>≋ eq-force-x)) 
   dia-sound-while-later {x} {b} {c} {v} l↯⊥ dia l⇓s=>⊆ w↯ | now (just s') with w↯
   ... | laterₗ w↯' rewrite eq-force-x with w↯'
   ... | laterₗ w↯'' = dia-sound (while b c) s' v v dia (l⇓s=>⊆ (laterₗ (≡=>≋ eq-force-x))) w↯''
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
    ```
      ]
    ]
  ]
#block(breakable: false)[
  #refproof(label: <proof-apfold-safe>, thmref: <thm-apfold-safe>)[
    #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/PureFolding/Arith.agda#L31")[
      ```hs
 -- Pure constant folding preserves semantics.
 apfold-safe : ∀ a s -> (aeval a s ≡ aeval (apfold a) s)
 apfold-safe (const n) _ = refl
 apfold-safe (var id) _ = refl
 apfold-safe (plus a₁ a₂) s 
  rewrite (apfold-safe a₁ s) 
  rewrite (apfold-safe a₂ s)  
  with (apfold a₁) in eq-a₁ | (apfold a₂) in eq-a₂
 ... | const n | const n₁  = refl
 ... | const n | var id     = refl
 ... | const n | plus v₂ v₃ = refl
 ... | var id     | v₂ = refl
 ... | plus v₁ v₃ | v₂ = refl
      ```
      ]
    ]
]

#block(breakable: false)[
  #refproof(label: <proof-bpfold-safe>, thmref: <thm-bpfold-safe>)[
    #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/PureFolding/Bool.agda#L38")[
      ```hs
 bpfold-safe : ∀ b s  -> (beval b s ≡ beval (bpfold b) s)
 bpfold-safe (const b) s  = refl
 bpfold-safe (le a₁ a₂) s rewrite (apfold-safe a₁ s) rewrite (apfold-safe a₂ s) 
  with (apfold a₁) | (apfold a₂)
 ... | const n | const n₁ = refl
 ... | const n | var id = refl
 ... | const n | plus v₂ v₃ = refl
 ... | var id | v₂ = refl
 ... | plus v₁ v₃ | v₂ = refl
 bpfold-safe (not b) s rewrite (bpfold-safe b s) with (bpfold b) 
 ... | const b₁ = refl
 ... | le a₁ a₂ = refl
 ... | not v = refl
 ... | and v v₁ = refl
 bpfold-safe (and b₁ b₂) s rewrite (bpfold-safe b₁ s) rewrite (bpfold-safe b₂ s) 
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
    ]
  ]

#block(breakable: false)[
  #refproof(label: <proof-cpfold-safe>, thmref: <thm-cpfold-safe>)[
    #mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/PureFolding/Command.agda#L50")[
      ```hs
  cpfold-safe : ∀ (c : Command) (s : Store) -> ∞ ⊢ (ceval c s) ≋ (ceval (cpfold c) s)
  cpfold-safe skip s rewrite (cpfold-skip) = now refl 
  cpfold-safe (assign id a) s = ≡=>≋ (cpfold-assign a id s)
  cpfold-safe (ifelse b cᵗ cᶠ) s = cpfold-if b cᵗ cᶠ s
  cpfold-safe (seq c₁ c₂) s = cpfold-seq c₁ c₂ s
  cpfold-safe (while b c) s = cpfold-while b c s 
  cpfold-assign : ∀ (a : AExp) (id : Ident) (s : Store) 
   -> (ceval (assign id a) s) ≡ (ceval (cpfold (assign id a)) s)
  cpfold-assign a id s 
   with (apfold-sound a s)
  ... | asound 
   with (aeval a s) in eq-av
  ... | nothing
   rewrite eq-av
   rewrite (eqsym asound)
   with (apfold a) in eq-ap
  ... | var id₁ rewrite eq-ap rewrite eq-av rewrite eq-av = eqrefl
  ... | plus n n₁ rewrite eq-ap rewrite eq-av rewrite eq-av = eqrefl
  cpfold-assign a id s | asound | just x 
   rewrite eq-av 
   rewrite (eqsym asound)
   with (apfold a) in eq-ap
  ... | var id₁ rewrite eq-ap rewrite eq-av rewrite eq-av = eqrefl
  cpfold-assign a id s | asound | just x | plus n n₁ 
   rewrite eq-ap rewrite eq-av rewrite eq-av = eqrefl
  cpfold-assign a id s | asound | just x | const n
   rewrite eq-ap rewrite eq-av rewrite eq-av 
   with asound 
  ... | eqrefl = eqrefl 
  cpfold-if : ∀ (b : BExp) (cᵗ cᶠ : Command) (s : Store) 
   -> ∞ ⊢ (ceval (ifelse b cᵗ cᶠ) s) ≋ (ceval (cpfold (ifelse b cᵗ cᶠ)) s)
  cpfold-if b cᵗ cᶠ s
   with (bpfold-sound b s)
  ... | bsound   
   with (beval b s) in eq-b
  ... | nothing 
   rewrite eq-b 
   rewrite (eqsym bsound) 
   with (bpfold b) in eq-bp
  ... | le a₁ a₂ rewrite eq-bp rewrite eq-b rewrite eq-b = now eqrefl
  ... | not n rewrite eq-bp rewrite eq-b rewrite eq-b = now eqrefl
  ... | and n n₁ rewrite eq-bp rewrite eq-b rewrite eq-b = now eqrefl
  -- cont 
      ```
      ]
    ]
  ]
//typstfmt::on
