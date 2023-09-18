#import "/includes.typ":*
#import "@preview/prooftrees:0.1.0"

#let conv(c, v) = { $#c arrow.b.double #v$ }
#let div(c) = { $#c arrow.t.double$ }
#let fails(c) = { $#c arrow.zigzag$ }


=== Definite initialization analysis<subsection-imp-analysis_optimization-dia>
The first operationn we describe is *definite initialization analysis*. In
general, the objective of this analysis is to ensure that no variable is ever
used before being initialized, which is the kind of failure, among many, we
chose to model.

==== Variables and indicator functions<subsubsection-imp-dia-vars>
This analysis deals with variables. Before delving into its details, we show
first a function to compute the set of variables used in arithmetic and boolean
expressions. The objective is to come up with a _set_ of identifiers that appear
in the expression: we chose to represent sets in Agda using indicator functions,
which we trivially define as parametric functions from a parametric set to the
set of booleans, that is ```hs IndicatorFunction = A -> Bool```; later, we will
instantiate this type for identifiers, giving the resulting type the name of
```hs VarsSet```. Foremost, we give a (parametric) notion of members equivalence
(that is, a function ```hs _==_ : A -> A -> Bool```); then, we equip indicator
functions of the usual operations on sets: insertion, union, and intersection
and define the usual property of inclusion.

#figure(```hs
∅ : IndicatorFunction
∅ = λ _ -> false

_↦_ : (v : A) -> (s : IndicatorFunction) -> IndicatorFunction
(v ↦  s) x = (v == x) ∨ (s x)

_∪_ : (s₁ s₂ : IndicatorFunction) -> IndicatorFunction
(s₁ ∪ s₂) x = (s₁ x) ∨ (s₂ x)

_∩_ : (s₁ s₂ : IndicatorFunction) -> IndicatorFunction
(s₁ ∩ s₂) x = (s₁ x) ∧ (s₂ x)

_⊆_ : (s₁ s₂ : IndicatorFunction) -> Set a
s₁ ⊆ s₂ = ∀ x -> (x-in-s₁ : s₁ x ≡ true) -> s₂ x ≡ true
```, caption: "Implementation of indicator functions in Agda")<code-indicator-function>

//typstfmt::off
Important properties of ```hs IndicatorFunction```s (and thus of ```hs VarsSet```s) follows.
//typstfmt::on
#theorem(
  name: "Equivalence of indicator functions",
)[

    (using the *Axiom of extensionality*)

//typstfmt::off
```hs
if-ext : ∀ {s₁ s₂ : IndicatorFunction} -> (a-ex : ∀ x -> s₁ x ≡ s₂ x) -> s₁ ≡ s₂
```
//typstfmt::on
<thm-if-equiv>
]
#theorem(name: "Neutral element of union")[
//typstfmt::off
```hs 
∪-∅ : ∀ {s : IndicatorFunction} -> (s ∪ ∅) ≡ s
```
//typstfmt::on
<thm-if-neutral-union>
]

#theorem(name: "Update inclusion")[
//typstfmt::off
```hs 
↦=>⊆ : ∀ {id} {s : IndicatorFunction} -> s ⊆ (id ↦ s)
```
//typstfmt::on
]
#theorem(name: "Transitivity of inclusion")[
//typstfmt::off
```hs
⊆-trans : ∀ {s₁ s₂ s₃ : IndicatorFunction} -> (s₁⊆s₂ : s₁ ⊆ s₂)
            -> (s₂⊆s₃ : s₂ ⊆ s₃) -> s₁ ⊆ s₃
```
//typstfmt::on
<thm-if-trans>
]

We will also need a way to get a ```hs VarsSet``` from a ```hs Store```, which
is shown in @code-store-domain.
#figure(```hs
dom : Store -> VarsSet
dom s x with (s x)
... | just _ = true
... | nothing = false
```, 
caption: [Code to compute the domain of a ```hs Store``` in Agda]
)<code-store-domain>

==== Realization<subsubsection-imp-dia-vars>
Following @concrete-semantics, the first formal tool we need is a means to
compute the set of variables mentioned in expressions, shown in
@code-avars-bvars; we also need a function to compute the set of variables that
are definitely initialized in commands, which is shown in @code-cvars.

#figure(
  tablex(
    columns: 2,
    align: center + horizon,
    auto-vlines: false,
    auto-hlines: false,
    [```hs
            avars : (a : AExp) -> VarsSet
            avars (const n) = ∅
            avars (var id) = id ↦ ∅
            avars (plus a₁ a₂) =
                  (avars a₁) ∪ (avars a₂)
                          ```],
    [
      ```hs
            bvars : (b : BExp) -> VarsSet
            bvars (const b) = ∅
            bvars (le a₁ a₂) =
                  (avars a₁) ∪ (avars a₂)
            bvars (not b) = bvars b
            bvars (and b b₁) =
                  (bvars b) ∪ (bvars b₁)
                      ```
    ],
  ),
  caption: "Agda code to compute variables in arithmetic and boolean expressions",
  supplement: "Listing",
)<code-avars-bvars>

#figure(
  ```hs
    cvars : (c : Command) -> VarsSet
    cvars skip = ∅
    cvars (assign id a) = id ↦ ∅
    cvars (seq c c₁) = (cvars c) ∪ (cvars c₁)
    cvars (ifelse b c c₁) = (cvars c) ∩ (cvars c₁)
    cvars (while b c) =  ∅
    ```,
  caption: "Agda code to compute initialized variables in commands",
  supplement: "Listing",
)<code-cvars>


#thmref(<ceval-store-inclusion>)[Theorem] allows us to show the following theorem. 
#theorem(
    name: [`ceval` adds at least the variables in commands]
    )[

    Let $c$ be a command and $sigma_1$ and $sigma_2$ be two stores. Then
    $ #conv($"ceval" c space sigma_1$, $sigma_2$) -> ("dom" sigma_1 union
    ("cvars" c)) space subset.eq ("dom" sigma_2) $
In Agda:
```hs
ceval⇓=>sc⊆s' :  ∀ (c : Command) (s s' : Store) (h⇓ : (ceval c s) ⇓ s') 
                  -> (dom s ∪ (cvars c)) ⊆ (dom s')
```
]

We now give inference rules that inductively build the relation that embodies
the logic of the definite initialization analysis, shown in @imp-dia-rel. In
Agda, we define a datatype representing the relation of type 
//typstfmt::off
```hs Dia : VarsSet -> Command -> VarsSet -> Set```, 
//typstfmt::on
which is shown in @code-dia.

#figure(
  tablex(
    columns: 2,
    align: center + horizon,
    auto-vlines: false,
    auto-hlines: false,
    prooftrees.tree(prooftrees.axi[], prooftrees.uni[Dia v skip v]),
    prooftrees.tree(
      prooftrees.axi[avars $a$ $subset.eq$ $v$],
      prooftrees.uni[Dia $v$ (assign $id$ $a$) ($id ↦ v$)],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [Dia $v_1$ $c_1$ $v_2$])),
      prooftrees.axi(pad(bottom: 2pt, [Dia $v_2$ $c_2$ $v_3$])),
      prooftrees.nary(2)[Dia $v_1$ (seq $c_1$ $c_2$) $v_3$],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [bvars $b$ $subset.eq$ $v$])),
      prooftrees.axi(pad(bottom: 2pt, [Dia $v$ $c^t$ $v^t$])),
      prooftrees.axi(pad(bottom: 2pt, [Dia $v$ $c^f$ $v^f$])),
      prooftrees.nary(
        3,
      )[#pad(top: 2pt, [Dia $v$ (if $b$ then $c^t$ else $c^f$) ($v^t sect v^f$)])],
    ),
    colspanx(2)[
      #prooftrees.tree(
        prooftrees.axi(pad(bottom: 2pt, [bvars $b$ $subset.eq$ $v$])),
        prooftrees.axi(pad(bottom: 2pt, [Dia $v$ $c$ $v_1$])),
        prooftrees.nary(2)[Dia $v$ (while $b$ $c$) $v$],
      )
    ],
  ),
  caption: "Inference rules for the definite initialization analysis",
  supplement: "Table",
)<imp-dia-rel>
#figure(```hs
  data Dia : VarsSet -> Command -> VarsSet -> Set where
   skip : ∀ (v : VarsSet) -> Dia v (skip) v
   assign : ∀ a v id (a⊆v : (avars a) ⊆ v) -> Dia v (assign id a) (id ↦ v)
   seq : ∀ v₁ v₂ v₃ c₁ c₂ -> (relc₁ : Dia v₁ c₁ v₂) ->
          (relc₂ : Dia v₂ c₂ v₃) -> Dia v₁ (seq c₁ c₂) v₃
   if : ∀ b v vᵗ vᶠ cᵗ cᶠ (b⊆v : (bvars b) ⊆ v) -> (relcᶠ : Dia v cᶠ vᶠ) ->
          (relcᵗ : Dia v cᵗ vᵗ) -> Dia v (ifelse b cᵗ cᶠ) (vᵗ ∩ vᶠ)
   while : ∀ b v v₁ c -> (b⊆s : (bvars b) ⊆ v) ->
          (relc : Dia v c v₁) -> Dia v (while b c) v
      ```, caption: "Dia relation in Agda")<code-dia>

What we want to show now is that if ```hs Dia``` holds, then the evaluation of a
command $c$ does not result in an error: while #thmref(<thm-adia-sound>)[Theorem] and
#thmref(<thm-bdia-sound>)[Theorem] show that if the variables in an arithmetic
expression or a boolean expression are contained in a store the result of their
evaluation can't be a failure (i.e. they result in "just" something), #thmref(<thm-cdia-sound>)[Theorem] shows
that if ```hs Dia``` holds, then the evaluation of a program failing is absurd.

#theorem(
  name: "Soundness of definite initialization for arithmetic expressions",
)[
    ```hs
    adia-sound : ∀ (a : AExp) (s : Store) (dia : avars a ⊆ dom s)
                  -> (∃ λ v -> aeval a s ≡ just v)
    ```
    <thm-adia-sound>
  ]

#theorem(name: "Soundness of definite initialization for boolean expressions")[
  ```hs
  bdia-sound : ∀ (b : BExp) (s : Store) (dia : bvars b ⊆ dom s)
                -> (∃ λ v -> beval b s ≡ just v)
  ```
  <thm-bdia-sound>
]

#theorem(
  name: "Soundness of definite initialization for commands",
)[
    ```hs
    dia-sound : ∀ (c : Command) (s : Store) (v v' : VarsSet) (dia : Dia v c v')
      (v⊆s : v ⊆ dom s) -> (h-err : (ceval c s) ↯) -> ⊥
    ```
    <thm-cdia-sound>
  ]
Here, we show the proof of #thmref(<thm-cdia-sound>)[Theorem]:
#proof[
    ```hs
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
    ```
  ]
