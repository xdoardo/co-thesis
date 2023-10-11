#import "/includes.typ":*
#import "@preview/prooftrees:0.1.0"

#let bisim = "≋"
#let conv(c, v) = { $#c arrow.b.double #v$ }
#let div(c) = { $#c arrow.t.double$ }
#let fails(c) = { $#c arrow.zigzag$ }

#linebreak()
=== Definite initialization analysis<subsection-imp-analysis_optimization-dia>
The first transformation we describe is *definite initialization analysis*. In
general, the objective of this analysis is to ensure that no variable is ever
used before being initialized, which is exactly the only kind of failure we
chose to model.

==== Variables and indicator functions<subsubsection-imp-dia-vars>
This analysis deals with variables. Before delving into its details, we show
first a function to compute the set of variables used in arithmetic and boolean
expressions. The objective is to come up with a _set_ of identifiers that appear
in the expression: we chose to represent sets in Agda using characteristic
functions, which we simply define as parametric functions from a parametric set
to the set of booleans, that is ```hs CharacteristicFunction = A -> Bool```;
later, we will instantiate this type for identifiers, giving the resulting type
the name of ```hs VarsSet```. First, we give a (parametric) notion of members
equivalence (that is, a function ```hs _==_ : A -> A -> Bool```); then, we the
usual operations on sets (insertion, union, and intersection) and the usual
definition of inclusion for characteristic functions.

#mycode(label: <code-charfun>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Data/CharacteristicFunction.agda#L13")[
//typstfmt::off
```hs
module Data.CharacteristicFunction {a} (A : Set a) (_==_ : A -> A -> Bool) where
-- ...
CharacteristicFunction : Set a
CharacteristicFunction = A -> Bool 
-- ...

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
  label: <thm-cf-equiv>
)[

  (using the *Axiom of extensionality*)
#mycode(proof: <proof-cf-equiv>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Data/CharacteristicFunction.agda#L48")[
//typstfmt::off
```hs
cf-ext : ∀ {s₁ s₂ : CharacteristicFunction} 
    (a-ex : ∀ x -> s₁ x ≡ s₂ x) -> s₁ ≡ s₂
```
//typstfmt::on
]] 

#theorem(name: "Neutral element of union", 
label: <thm-if-neutral-union>)[
#mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Data/CharacteristicFunction.agda#L58")[
//typstfmt::off
```hs
∪-∅ : ∀ {s : CharacteristicFunction} -> (s ∪ ∅) ≡ s
```
//typstfmt::on
]] 

#theorem(name: "Update inclusion")[
#mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Data/CharacteristicFunction.agda#L61")[
//typstfmt::off
```hs
↦=>⊆ : ∀ {id} {s : CharacteristicFunction} -> s ⊆ (id ↦ s)
```
//typstfmt::on
]]
#theorem(name: "Transitivity of inclusion", label: <thm-cf-trans> )[
#mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Data/CharacteristicFunction.agda#L87")[
//typstfmt::off
```hs
⊆-trans : ∀ {s₁ s₂ s₃ : CharacteristicFunction} -> (s₁⊆s₂ : s₁ ⊆ s₂)
            -> (s₂⊆s₃ : s₂ ⊆ s₃) -> s₁ ⊆ s₃
```
//typstfmt::on
]] 

We will also need a way to get a ```hs VarsSet``` from a ```hs Store```, which
is shown in @code-store-domain.
#mycode(label: <code-store-domain>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Vars.agda#L35")[
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
Following @concrete-semantics, the first formal tool we need is a way to
compute the set of variables mentioned in expressions, shown in
@code-avars and @code-bvars. We also need a function to compute the set of variables that
are definitely initialized in commands, which is shown in @code-cvars.
#grid(
columns: 2,
//align: center + horizon,
//auto-vlines: false,
//auto-hlines: false,
gutter: 5pt, 
mycode(label: <code-avars>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Vars.agda#L16")[
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
mycode(label: <code-bvars>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Vars.agda#L21")[
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
#mycode(label: <code-cvars>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Vars.agda#L27")[
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

It is worth to reflect upon the definition of @code-cvars. This 
code computes the set of _initialized_ variables in a command `c`; as
done in @concrete-semantics, we construct this set of initialized variables in
the most conservative way possible: of course, `skip` does not have any initialized
variable and `assign id a` adds `id` to the set of initialized variables. 

However, when considering composite commands, we must consider that, except for
`seq c c₁`, not every branch of execution is taken; this means that we cannot
know statically whether `ifelse b cᵗ cᶠ` will lead to the execution to the
execution of `cᵗ` or `cᶠ`, we thus take the intersection of their initialized
variables, that is we compute the set of variables that will be surely
initialized wheter one or the other executes. The same reasoning applies to
`while b c`: we cannot possibly know whether or not `c` will ever execute, thus
we consider no new variables initialized.

At this point it should be clear that as `cvars c` computes the set of
initialized variables in a conservative fashion, it is not necessarily true
that the actual execution of the command will not add additional variables:
however, knowing that if the evaluation of a command in a store $sigma$
converges to a value $sigma'$, that is $#conv([$c$, $sigma$], $sigma'$)$ then by
@lemma-ceval-store-tilde[Lemma] $"dom" sigma subset.eq "dom" sigma'$;
this allows us to show the following lemma.

#lemma(label: <lemma-ceval-sc-subeq>)[
    Let $c$ be a command and $sigma$ and $sigma'$ be two stores. Then
    #align(center, 
    $#conv($"ceval" c space sigma$, $sigma'$) -> ("dom" sigma_1 union
    ("cvars" c)) space subset.eq ("dom" sigma')$)

#mycode(proof: <proof-ceval-sc-subeq>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Semantics/BigStep/Functional/Properties.agda#L133")[
//typstfmt::off
```hs
ceval⇓=>sc⊆s' :  ∀ (c : Command) (s s' : Store) (h⇓ : (ceval c s) ⇓ s')
                  -> (dom s ∪ (cvars c)) ⊆ (dom s')
```
//typstfmt::on 
]] 


We now give inference rules that inductively build the relation that embodies
the logic of the definite initialization analysis, shown in @imp-dia-rel. In
Agda, we define a datatype representing the relation of type
//typstfmt::off
```hs Dia : VarsSet -> Command -> VarsSet -> Set```,
//typstfmt::on
which is shown in @code-dia. @lemma-ceval-sc-subeq[Lemma]
will allow us to show that there  is a relation between  the `VarsSet` in the
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
#mycode(label: <code-dia>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L22")[
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
@thm-adia-safe and @thm-bdia-safe show
that if the variables in an arithmetic expression or a boolean expression are
contained in a store the result of their evaluation cannot be a failure (i.e.
they result in "just" something, as it cannot diverge),
@thm-dia-safe shows that if ```hs Dia``` holds, then the
evaluation of a program failing is absurd: therefore, by
@post-exec, the program either diverges or converges to some
value.

#theorem( name: "Safety of arithmetic expressions", label: <thm-adia-safe>)[
#mycode(proof: <proof-adia-safe>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L47")[
//typstfmt::off
```hs 
adia-safe : ∀ (a : AExp) (s : Store) (dia : avars a ⊆ dom s)
                  -> (∃ λ v -> aeval a s ≡ just v)
```
//typstfmt::on
]] 

#theorem(name: "Safety of boolean expressions", label: <thm-bdia-safe>)[
 #mycode(proof: <proof-bdia-safe>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L60")[
//typstfmt::off
```hs
bdia-safe : ∀ (b : BExp) (s : Store) (dia : bvars b ⊆ dom s)
              -> (∃ λ v -> beval b s ≡ just v)
```
//typstfmt::on
]] 

#theorem(
  name: "Safety of definite initialization for commands",
  label: <thm-dia-safe>
)[
#mycode(proof: <proof-dia-safe>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L117")[
//typstfmt::off
```hs
dia-safe : ∀ (c : Command) (s : Store) (v v' : VarsSet) (dia : Dia v c v')
  (v⊆s : v ⊆ dom s) -> (h-err : (ceval c s) ↯) -> ⊥
```
//typstfmt::on
]] 

We now show an idea of the proof (the full proof, in Agda, is in
@proof-dia-safe), examining the two base cases `c ≡ skip` and `c ≡ assign id a`
and the coinductive case `c ≡ while b c'`. The proof for the base cases is, in
words, based on the idea that the evaluation cannot possibly go wrong: note
that by the hypotheses, we have that `(ceval c s) ↯`, which we can express in
math as $ceval space c space sigma bisim now nothing$.


#show figure.where(kind: "boxenv"): set block(breakable: true)
#proof[
  1. Let $c$ be the command `skip`. Then, for any store $sigma$, by the
    definition of `ceval` in @code-ceval and by the inference rule $arrow.b.double$skip in
    @imp-commands-semantics, the evaluation of $c$ in the store $sigma$ must be 
    #align(center, $ceval "skip" sigma eq.triple now (just sigma)$)

    Given the hypothesis that #fails([c, $sigma$]), we now have that it must be
    $now nothing bisim now (just sigma )$, which is false for any $sigma$, making the hypothesis
    #fails([c, $sigma$]) impossible.
  2. Let $c$ be the command `assign id a`, for some identifier $id$ and
    arithmetic expression $a$. By the hypothesis, we have that it must be $"Dia"
    v space (assign id a) space v'$ for some $v$ and $v'$, which entails that
    the variables that appear in $a$, which we named $"avars" a$, are all
    initialized in $v$, that is $"avars" a subset.eq v$; this and the
    hypothesis that $v subset.eq "dom" sigma$ imply by @thm-cf-trans
    that $"avars" a subset.eq "dom" sigma$.

    By @thm-adia-safe, with the assumption that $"avars" a subset.eq "dom" sigma$, 
    it must be $aeval a sigma eq.triple just n$ for some $n : ZZ$. Again, by the 
    definition of `ceval` in @code-ceval and by the inference rule $arrow.b.double$assign 
    in @imp-commands-semantics, the evaluation of $c$ in the store $sigma$ must be 

    #align(center, $ceval (assign id a) space sigma eq.triple now (just ("update"
    id n space sigma))$)

    and, as before, by the hypothesis that $c$ fails it must thus be that $now
    nothing bisim now (just ("update" id n space sigma))$, which is impossible for any $sigma$, 
    making the hypotesis #fails([c]) impossible.

  3. Let $c$ be the command `while b c'` for some boolean expression $b$ and
    some command $c'$. By @thm-bdia-safe, with the assumption that $"bvars" b
    subset.eq "dom" sigma$, it must be $"beval" b space sigma eq.triple "just" v$ for some
    $v : BB$. 

    #linebreak()
    If $v eq.triple "false"$, then by the  definition of `ceval` in
    @code-ceval and by the inference rule $arrow.b.double$while-false in
    @imp-commands-semantics, the evaluation of $c$ in the store $sigma$ must be 

    #align(center, $ceval ("while" b space c') space sigma eq.triple now ("just" sigma)$)

    making the hypothesis that the evaluation of $c$ fails impossible. 

    #linebreak()
    If, instead, $v eq.triple "true"$, we must evaluate $c'$ in $sigma$. 
    The case $c' eq.triple now nothing$ is impossible by the inductive hypothesis.

    #linebreak()
    If $c' eq.triple now (just sigma')$ for some $sigma'$, then, by recursion, it must be
    #align(center, [```hs dia-sound (while b c) s' v v dia (⊆-trans v⊆s (ceval⇓=>⊆ c s s' (≡=>≋ eq-ceval-c))) w↯```])

    #linebreak()
    Finally, if $c' eq.triple "later" x$ for some $x$, then we can prove inductively that  
#mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/DefiniteInitialization.agda#L165", proof: <proof-dia-sound-while-later>)[
//typstfmt::off
```hs
dia-sound-while-later : ∀ {x : Thunk (Delay (Maybe Store)) ∞} {b c} {v} 
 (l↯⊥ : (later x)↯ -> ⊥) (dia : Dia v (while b c) v) 
 (l⇓s=>⊆ : ∀ {s : Store} -> ((later x) ⇓ s) -> v ⊆ dom s)
 (w↯ : (bind (later x) (λ s -> later (ceval-while c b s))) ↯) -> ⊥
```
//typstfmt::on
] ]

The proof works by unwinding, inductively, the assumption that #fails([c]): if
it fails, then $ceval space c space sigma$ must eventually converge to $"now" space "nothing"$.
The proof thus works by showing base cases and, in the case of $"seq" space c_1 space c_2$
and $"while" space b space c' space eq.triple space "if" space b space "then" space ("seq" space c' space ("while" space b space c')) space "else" space "skip"$, 
showing that by inductive hypotesis $c_1$ or $c'$ cannot possibly fail; then,
the assumption becomes that it is the second command ($c_2$ or $"while" space b space c'$)
that fails, which we can inductively show absurd.

#show figure.where(kind: "boxenv"): set block(breakable: false)
