#import "/includes.typ":*
#import "@preview/prooftrees:0.1.0"

#let conv(c, v) = { $#c arrow.b.double #v$ }
#let div(c) = { $#c arrow.t.double$ }
#let fails(c) = { $#c arrow.zigzag$ }

=== Definite initialization analysis<subsection-imp-analysis_optimization-dia>
The first transformation we describe is *definite initialization analysis*. In
general, the objective of this analysis is to ensure that no variable is ever
used before being initialized, which is the kind of failure, among many, we
chose to model.

==== Variables and indicator functions<subsubsection-imp-dia-vars>
This analysis deals with variables. Before delving into its details, we show
first a function to compute the set of variables used in arithmetic and boolean
expressions. The objective is to come up with a _set_ of identifiers that appear
in the expression: we chose to represent sets in Agda using characteristic
functions, which we simply define as parametric functions from a parametric set
to the set of booleans, that is ```hs CharacteristicFunction = A -> Bool```;
later, we will instantiate this type for identifiers, giving the resulting type
the name of ```hs VarsSet```. Foremost, we give a (parametric) notion of members
equivalence (that is, a function ```hs _==_ : A -> A -> Bool```); then, we equip
characteristic functions of the usual operations on sets: insertion, union, and
intersection and the usual definition of inclusion.

#mycode(ref: <code-charfun>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Data/CharacteristicFunction.agda#L13")[
//typstfmt::off
```hs
∅ : CharacteristicFunction
∅ = λ _ -> false

_↦_ : (v : A) -> (s : CharacteristicFunction) -> CharacteristicFunction
(v ↦ s) x = (v == x) ∨ (s x)

_∪_ : (s₁ s₂ : CharacteristicFunction) -> CharacteristicFunction
(s₁ ∪ s₂) x = (s₁ x) ∨ (s₂ x)

_∩_ : (s₁ s₂ : CharacteristicFunction) -> CharacteristicFunction
(s₁ ∩ s₂) x = (s₁ x) ∧ (s₂ x)

_⊆_ : (s₁ s₂ : CharacteristicFunction) -> Set a
s₁ ⊆ s₂ = ∀ x -> (x-in-s₁ : s₁ x ≡ true) -> s₂ x ≡ true
```
//typstfmt::on
]

#theorem(
  name: "Equivalence of characteristic functions",
)[

  (using the *Axiom of extensionality*)
#mycode(proof: <proof-cf-equiv>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Data/CharacteristicFunction.agda#L48")[
//typstfmt::off
```hs
cf-ext : ∀ {s₁ s₂ : CharacteristicFunction} 
    (a-ex : ∀ x -> s₁ x ≡ s₂ x) -> s₁ ≡ s₂
```
//typstfmt::on
]
<thm-cf-equiv>
]

#theorem(name: "Neutral element of union")[
#mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Data/CharacteristicFunction.agda#L58")[
//typstfmt::off
```hs
∪-∅ : ∀ {s : CharacteristicFunction} -> (s ∪ ∅) ≡ s
```
//typstfmt::on
]
<thm-if-neutral-union>
]

#theorem(name: "Update inclusion")[
#mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Data/CharacteristicFunction.agda#L61")[
//typstfmt::off
```hs
↦=>⊆ : ∀ {id} {s : CharacteristicFunction} -> s ⊆ (id ↦ s)
```
//typstfmt::on
]
]
#theorem(name: "Transitivity of inclusion")[
#mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Data/CharacteristicFunction.agda#L87")[
//typstfmt::off
```hs
⊆-trans : ∀ {s₁ s₂ s₃ : CharacteristicFunction} -> (s₁⊆s₂ : s₁ ⊆ s₂)
            -> (s₂⊆s₃ : s₂ ⊆ s₃) -> s₁ ⊆ s₃
```
//typstfmt::on
]
<thm-if-trans>
]

We will also need a way to get a ```hs VarsSet``` from a ```hs Store```, which
is shown in #coderef(<code-store-domain>).
#mycode(ref: <code-store-domain>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Vars.agda#L35")[
//typsfmt::off
```hs
dom : Store -> VarsSet
dom s x with (s x)
... | just _ = true
... | nothing = false
```
//typstfmt::on
]

==== Realization<subsubsection-imp-dia-vars>
Following @concrete-semantics, the first formal tool we need is a means to
compute the set of variables mentioned in expressions, shown in
#coderef(<code-avars>) and #coderef(<code-bvars>). We also need a function to compute the set of variables that
are definitely initialized in commands, which is shown in #coderef(<code-cvars>).
#grid(
columns: 2,
//align: center + horizon,
//auto-vlines: false,
//auto-hlines: false,
gutter: 5pt, 
mycode(ref: <code-avars>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Vars.agda#L16")[
//typstfmt::off
```hs
avars : (a : AExp) -> VarsSet
avars (const n) = ∅
avars (var id) = id ↦ ∅
avars (plus a₁ a₂) = 
  (avars a₁) ∪ (avars a₂)
```
//typstfmt::on
],
mycode(ref: <code-bvars>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Vars.agda#L21")[
//typstfmt::off
```hs
bvars : (b : BExp) -> VarsSet
bvars (const b) = ∅
bvars (le a₁ a₂) =
      (avars a₁) ∪ (avars a₂)
bvars (not b) = bvars b
bvars (and b b₁) =
      (bvars b) ∪ (bvars b₁)
```
//typstfmt::on
])
#mycode(ref: <code-cvars>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Vars.agda#L27")[
//typstfmt::off
```hs
cvars : (c : Command) -> VarsSet
cvars skip = ∅
cvars (assign id a) = id ↦ ∅
cvars (seq c c₁) = (cvars c) ∪ (cvars c₁)
cvars (ifelse b cᵗ cᶠ) = (cvars cᵗ) ∩ (cvars cᶠ)
cvars (while b c) =  ∅
```
//typstfmt::on
]

It is worth to reflect upon the definition of #coderef(<code-cvars>). What this
code does it compute the set of _initialized_ variables in a command `c`; as
done in @concrete-semantics, we construct this set of initialized variables in
the most careful way possible: of course, `skip` does not have any initialized
variable and `assign id a` adds `id` to the set of initialized variables. 

However, when considering composite commands, we must consider that, except for
`seq c c₁`, not every branch of execution is taken; this means that we cannot
know statically whether `ifelse b cᵗ cᶠ` will lead to the execution to the
execution of `cᵗ` or `cᶠ`, we thus take the intersection of their initialized
variables, that is we compute the set of variables that will be surely
initialized wheter one or the other executes. The same reasoning applies to
`while b c`: we cannot possibly know whether or not `c` will ever execute, thus
we consider no new variables initialized.

At this point it should be clear that `cvars c` computes the set of initialized
variables in a conservative fashion, it is not necessarily true that the actual
execution of the command will not add additional variables: however, knowing
that if a the evaluation of a command in a store $sigma$ converges to a value
$sigma'$, that is $#conv([$c$, $sigma$], $sigma'$)$ then by
#thmref(<lemma-ceval-store-tilde>)[Lemma] $"dom" sigma subset.eq "dom" sigma'$;
this allows us to show the following lemma.

#lemma()[
    Let $c$ be a command and $sigma_1$ and $sigma_2$ be two stores. Then
    #align(center, 
    $#conv($"ceval" c space sigma_1$, $sigma_2$) -> ("dom" sigma_1 union
    ("cvars" c)) space subset.eq ("dom" sigma_2)$)

#mycode(proof: <proof-ceval-sc-subeq>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Semantics/BigStep/Functional/Properties.agda#L133")[
//typstfmt::off
```hs
ceval⇓=>sc⊆s' :  ∀ (c : Command) (s s' : Store) (h⇓ : (ceval c s) ⇓ s')
                  -> (dom s ∪ (cvars c)) ⊆ (dom s')
```
//typstfmt::on 
<lemma-ceval-sc-subeq>
]]


We now give inference rules that inductively build the relation that embodies
the logic of the definite initialization analysis, shown in @imp-dia-rel. In
Agda, we define a datatype representing the relation of type
//typstfmt::off
```hs Dia : VarsSet -> Command -> VarsSet -> Set```,
//typstfmt::on
which is shown in #coderef(<code-dia>). #thmref(<lemma-ceval-sc-subeq>)[Lemma]
will allow us to show that there's a relation between  the `VarsSet` in the
`Dia` relation and the actual stores that are used in the execution of a
command.

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
      prooftrees.axi(pad(bottom: 4pt, [Dia $v_1$ $c_1$ $v_2$])),
      prooftrees.axi(pad(bottom: 4pt, [Dia $v_2$ $c_2$ $v_3$])),
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
        prooftrees.axi(pad(bottom: 3pt, [bvars $b$ $subset.eq$ $v$])),
        prooftrees.axi(pad(bottom: 3pt, [Dia $v$ $c$ $v_1$])),
        prooftrees.nary(2)[Dia $v$ (while $b$ $c$) $v$],
      )
    ],
  ),
  caption: "Inference rules for the definite initialization analysis",
  supplement: "Table",
)<imp-dia-rel>
#mycode(ref: <code-dia>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L22")[
//typstfmt::off
```hs
data Dia : VarsSet -> Command -> VarsSet -> Set where
 skip : ∀ (v : VarsSet) -> Dia v (skip) v
 assign : ∀ a v id (a⊆v : (avars a) ⊆ v) -> Dia v (assign id a) (id ↦ v)
 seq : ∀ v₁ v₂ v₃ c₁ c₂ -> (relc₁ : Dia v₁ c₁ v₂) ->
        (relc₂ : Dia v₂ c₂ v₃) -> Dia v₁ (seq c₁ c₂) v₃
 if : ∀ b v vᵗ vᶠ cᵗ cᶠ (b⊆v : (bvars b) ⊆ v) -> (relcᶠ : Dia v cᶠ vᶠ) ->
        (relcᵗ : Dia v cᵗ vᵗ) -> Dia v (ifelse b cᵗ cᶠ) (vᵗ ∩ vᶠ)
 while : ∀ b v v₁ c -> (b⊆s : (bvars b) ⊆ v) ->
        (relc : Dia v c v₁) -> Dia v (while b c) v
```
//typstfmt::on
]

What we want to show now is that if ```hs Dia``` holds, then the evaluation of
a command $c$ does not result in an error: while
#thmref(<thm-adia-sound>)[Theorem] and #thmref(<thm-bdia-sound>)[Theorem] show
that if the variables in an arithmetic expression or a boolean expression are
contained in a store the result of their evaluation cannot be a failure (i.e.
they result in "just" something, as it cannot diverge),
#thmref(<thm-dia-sound>)[Theorem] shows that if ```hs Dia``` holds, then the
evaluation of a program failing is absurd: therefore, by
#thmref(<thm-exec>)[Theorem], the program either diverges or converges to some
value.

#theorem( name: "Soundness of definite initialization for arithmetic expressions")[
#mycode(proof: <proof-adia-sound>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L47")[
//typstfmt::off
```hs 
adia-sound : ∀ (a : AExp) (s : Store) (dia : avars a ⊆ dom s)
                  -> (∃ λ v -> aeval a s ≡ just v)
```
//typstfmt::on
] <thm-adia-sound> ]

#theorem(name: "Soundness of definite initialization for boolean expressions")[
 #mycode(proof: <proof-bdia-sound>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L60")[
//typstfmt::off
```hs
bdia-sound : ∀ (b : BExp) (s : Store) (dia : bvars b ⊆ dom s)
              -> (∃ λ v -> beval b s ≡ just v)
```
//typstfmt::on
] <thm-bdia-sound> ]

#theorem(
  name: "Soundness of definite initialization for commands",
)[
#mycode(proof: <proof-dia-sound>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L117")[
//typstfmt::off
```hs
dia-sound : ∀ (c : Command) (s : Store) (v v' : VarsSet) (dia : Dia v c v')
  (v⊆s : v ⊆ dom s) -> (h-err : (ceval c s) ↯) -> ⊥
```
//typstfmt::on
] <thm-dia-sound> ]
We now show an idea of the proof in a discursive manner (the full proof, in
Agda, is in #coderef(<proof-dia-sound>)). Let us start with the two simple
(non-recursive) cases. The first is `c ≡ skip`, where we have the following situation:
#code()[
//typstfmt::off
```hs
 dia-sound' skip s v v' dia v⊆s h-err = {! !}
-- ————————————————————————————————————————————————————————————
-- Goal: ⊥
-- ————————————————————————————————————————————————————————————
-- dia : Dia v skip v'
-- h-err : WeakBisim _≡_ ∞ (ceval skip s) (now nothing)
-- s : Ident → Maybe ℤ
-- v v' : String → Bool
-- v⊆s : (x : String) → v x ≡ true → dom s x ≡ true
-- ————————————————————————————————————————————————————————————
```
//typstfmt::on
]
Forcing Agda to inspect `h-err`, we get the assumption that `just s ≡ nothing`;
inspecting this assumption we easily get #coderef(<dia-sound-skip>). 
#mycode(ref: <dia-sound-skip>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L119")[
//typstfmt::off
```hs
  dia-sound skip s v v' dia v⊆s (now ())
```
//typstfmt::on
  ]
Let us move to the second "easy" case, assignment: 
#code()[
//typstfmt::off
```hs 
dia-sound' (assign id a) s v v' dia v⊆s h-err = {! !}
-- ————————————————————————————————————————————————————————————
-- Goal: ⊥
-- ————————————————————————————————————————————————————————————
-- a : AExp
-- dia : Dia v (assign id a) v'
-- h-err : WeakBisim _≡_ ∞ (ceval (assign id a) s) (now nothing)
-- id : String
-- s : Ident → Maybe ℤ
-- v v' : String → Bool
-- v⊆s : (x : String) → v x ≡ true → dom s x ≡ true
-- ————————————————————————————————————————————————————————————
```
//typstfmt::on
]
We can make Agda aware of what `v'` is, that is, `v' ≡ (id ↦ v)` by splitting on `dia`:
#code()[
```hs
 dia-sound' (assign id a) s v .(id ↦ v) (assign .a .v .id a⊆v) v⊆s h-err = {! !}
```
]
And using the value of `aeval a s` using `adia-sound`
(#thmref(<thm-adia-sound>)[Theorem]) we conclude this piece of proof as shown in
#coderef(<dia-sound-assign>).
#mycode(ref: <dia-sound-assign>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L120")[
//typstfmt::off
```hs
  dia-sound (assign id a) s v .(id ↦ v) (assign .a .v .id a⊆v) v⊆s h-err 
   with (adia-sound a s (⊆-trans a⊆v v⊆s))
  ... | a' , eq-aeval 
   rewrite eq-aeval 
   rewrite eq-aeval 
   with h-err
  ... | now ()
```
//typstfmt::on
]

Let us examine a bit more difficult case, `while`, as shown in #coderef(<ex-dia-sound-while>).
//typstfmt::off
In this case, we proceed with the value of `beval b s` using `bdia-sound`
(#thmref(<thm-bdia-sound>)[Theorem]) we get to two outcomes: 
if `beval b s ≡ just false`, then `ceval (while b c) s` converges to `s` 
itself, and we get to the same absurd hypothesis `just s ≡ nothing`, which
concludes this branch of the proof.
//typstfmt::on
If, instead, `beval b s ≡ just true`, we consider the value of `ceval c s`
(#coderef(<dia-sound-while>)), which can have three outcomes: it can fail, that
is `ceval c s ≡ now nothing` and we conclude this branch of the proof with a
recursive call on `dia-sound c`; it can converge to `ceval c s ≡ now (just s)'`
and we conclude this branch of the proof with a recursive call on `dia-sound (while b c) s'`. 

#code(ref: <ex-dia-sound-while>)[
//typstfmt::off
```hs
 dia-sound' (while b c) s v v' dia v⊆s h-err = {! !}
-- ————————————————————————————————————————————————————————————
-- Goal: ⊥
-- ————————————————————————————————————————————————————————————
-- b : BExp
-- c : Command
-- dia : Dia v (while b c) v'
-- h-err : WeakBisim _≡_ ∞ (ceval (while b c) s) (now nothing)
-- s : Ident → Maybe ℤ
-- v v' : String → Bool
-- v⊆s : (x : String) → v x ≡ true → dom s x ≡ true
-- ————————————————————————————————————————————————————————————
```
//typstfmt::on
]

#mycode(ref: <dia-sound-while>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L149")[
//typstfmt::off
```hs
dia-sound (while b c) s v v' dia v⊆s h-err | true 
 with (ceval c s) in eq-ceval-c --- <- here
... | now nothing = dia-sound c s v v₁ dia-c v⊆s (≡=>≋ eq-ceval-c) 
dia-sound (while b c) s v v' dia v⊆s h-err | true | now (just s')  
 with h-err
... | laterₗ w↯ = 
 dia-sound (while b c) s' v v dia 
    (⊆-trans v⊆s (ceval⇓=>⊆ c s s' (≡=>≋ eq-ceval-c))) w↯
dia-sound (while b c) s v v' dia v⊆s h-err | true | later x 
 with (dia-sound c s v v₁ dia-c v⊆s)
... | c↯⊥  = dia-sound-while-later c↯⊥ dia h h-err 
```
//typstfmt::on
  ]
If, finally, `ceval c s ≡ later x`, we use an helper function (a lemma), shown
in #coderef(<dia-sound-while-later>).
#mycode(ref: <dia-sound-while-later>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L165")[
//typstfmt::off
```hs
dia-sound-while-force : ∀ {x : Thunk (Delay (Maybe Store)) ∞} {b c} {v} 
  (l↯⊥ : (force x)↯ -> ⊥) (dia : Dia v (while b c) v) 
  (l⇓s=>⊆ : ∀ {s : Store} -> ((force x) ⇓ s) -> v ⊆ dom s) 
  (w↯ : (bind (force x) (λ s -> later (ceval-while c b s))) ↯) -> ⊥
dia-sound-while-force {x} {b} {c} {v} l↯⊥ dia l⇓s=>⊆ w↯ 
 with (force x) in eq-force-x
... | now nothing = l↯⊥ w↯
dia-sound-while-force {x} {b} {c} {v} l↯⊥ dia l⇓s=>⊆ w↯ | now (just s') 
 rewrite eq-force-x 
 with w↯
... | laterₗ w↯' = 
 dia-sound (while b c) s' v v dia (l⇓s=>⊆ (now refl)) w↯'
dia-sound-while-force {x} {b} {c} {v} l↯⊥ dia l⇓s=>⊆ w↯ | later x₁ = 
 dia-sound-while-later {x₁} l↯⊥ dia l⇓s=>⊆ w↯
```
//typstfmt::on
]

What this last piece of code does is coinductively "unwind" the execution of
`while b c` to check whether or not `ceval c` in a generic store `s` converges
to a store `s'`; if so, then check that `ceval (while b c) s'` does not fail by
checking that `ceval c s'` does not fail and so on; while if `ceval c s` fails,
use the assumption that it can't fail (which is just a preventive call to
`dia-sound`).
