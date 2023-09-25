#import "/includes.typ": *

== Monads<section-monads>
In 1989, Eugenio Moggi published a paper @moggi-monads in which the term
_monad_, which was already used in the context of mathematics and, in
particular, category theory, was given meaning in the context of functional
programming. Explaining monads is, arguably, one the most discussed topics in
the pedagogy of computer science, and tons of articles, blog posts and books try
to explain the concept of monad in various ways.

A monad is a datatype equipped with (at least) two functions, `bind` (often
`_>>=_`) and `unit`; in general, we can see monads as a structure used to
combine computations. One of the most trivial instance of monad is the `Maybe`
monad, which we now present to investigate what monads are: in Agda, the `Maybe`
monad is composed of a datatype

#agdacode[
//typstfmt::off
```hs
data Maybe {a} (A : Set a) : Set a where
  just : A → Maybe A
  nothing : Maybe A
```
//typstfmt::on
]
and two functions representing its monadic features:

#agdacode[
//typstfmt::off
```hs
unit : A -> Maybe A
unit = just

_>>=_ : Maybe A → (A → Maybe B) → Maybe B
nothing >>= f = nothing
just a  >>= f = f a
```
//typstfmt::on
]

The `Maybe` monad is a structure that represents how to deal with computations
that may result in a value but may also result in nothing; in general, the line
of reasoning for monads is exactly this, they are a means to model a behaviour
of the execution, or *effects*: in fact, they're also called "computation
builders" in the context of programming. Let us give an example:
#agdacode[
//typstfmt::off
```hs
  h : Maybe ℕ → Maybe ℕ
  h x = x >>= λ v -> just (v + 1)
```
//typstfmt::on
]

The underlying idea of monads in the context of computer science, as explained
by Moggi in @moggi-monads, is to describe "notions of computations" that may
have consequences comparable to _side effects_ of imperative programming
languages in pure functional languages.

=== Formal definition<subsubsection-monad-formal_def>
We will now give a formal definition of what monads are. They're usually
understood in the context of category theory and in particular _Kleisli
triples_; here, we give a minimal definition inspired by @kohl-monads-cs.

#definition(
  name: "Monad",
)[
    Let $A$, $B$ and $C$ be types. A monad $M$ is defined as the triple (`M` ,
    `unit`, `_>>=_`) where `M` is a monadic constructor denoting some side-effect or
    impure behaviour; `unit : A -> M A` represents the identity function and 
    // typstfmt::off
    `_>>=_ : M A -> (A -> M B) -> M B` is used for monadic composition.
    //typstfmt::on

    The triple must satisfy the following laws.
    1. (*left identity*) For every `x : A` and `f : A -> M B`, `unit x >>= f` $eq.triple$ `f x`;
    2. (*right identity*) For every `mx : M A`, `mx >>= unit` $eq.triple$ `mx`; and
    3. (*associativity*) For every `mx : M A`, `f : A -> M B` and `g : B -> M C`,

      `(mx >>= f) >>= g` $eq.triple$ `mx >>= (λ my -> f my >>= g)`
  ]

== The Delay monad<subsection-monad-delay_monad>
In 2005, Venanzio Capretta introduced the `Delay` monad to represent recursive
(thus potentially infinite) computations in a coinductive (and monadic) fashion
@capretta-delay. As described in @abel-nbe, the `Delay` type is used to
represent computations whose result may be available with some _delay_ or never
be returned at all: the `Delay` type has two constructors; one, `now`, contains
the result of the computation. The second, `later`, embodies one "step" of delay
and, of course, an infinite (coinductive) sequence of `later` indicates a
non-terminating computation, practically making non-termination an effect.

In Agda, the `Delay` type is defined as follows (using _sizes_ and _levels_, see
@subsection-agda-sized_types[Subsection]):
#agdacode[
//typstfmt::off
```hs
data Delay {ℓ} (A : Set ℓ) (i : Size) : Set ℓ where
  now   : A → Delay A i
  later : Thunk (Delay A) i → Delay A i
```
//typstfmt::on
]
We equip with the following `bind` function:
#agdacode[
//typstfmt::off
```hs
 bind : ∀ {i} → Delay A i → (A → Delay B i) → Delay B i
 bind (now a)   f = f a
 bind (later d) f = later λ where .force → bind (d .force) f
```
//typstfmt::on
]
In words, what `bind` does, is this: given a `Delay A i` `x`, it checks whether
`x` contains an immediate result (i.e., `x ≡ now a`) and, if so, it applies the
function `f`; if, otherwise, `x` is a step of delay, (i.e., `x ≡ later d`),
`bind` delays the computation by wrapping the observation of `d` (represented
as ```hs d .force```) in the `later` constructor. Of course, this is the only
possibile definition: for example,
//typstfmt::off
```hs bind' (later d) f = bind' (d .force) f```
//typstfmt::on
would not pass the termination and productivity checker; in fact, take the
`never` term as shown in #coderef(<code-never>): of course,
//typstfmt::off
```hs bind' never f```
//typstfmt::on
would never terminate.

#agdacode(ref: <code-never>)[
//typstfmt::off
```hs
 never : ∀ {i} -> Delay A i
 never = later λ where .force -> never
```
//typstfmt::on
]

We might however argue that `bind` as well never terminates, in fact `never`
_never yields a value_ by definition; this is correct, but the two views on
non-termination are radically different. The detail is that `bind'` observes the
whole of `never` immediately, while `bind` leaves to the observer the job of
actually inspecting what the result of `bind x f` _is_, and this is the utility
of the `Delay` datatype and its monadic features.

== Bisimilarity<subsection-monad-bisimilarity>
Consider the following snippet. 
#mycode(
  ref: <code-comp-a>,
  "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/Delay/Examples.agda#L9",
)[
//typstfmt::off
```hs
comp-a : ∀ {i} -> Delay ℤ i
comp-a = now 0ℤ
```
//typstfmt::on
  ]
The term represents in #coderef(<code-comp-a>) a computation converging to the value `0` immediately, as
no `later` appears in its definition.
#mycode(
  ref: <code-comp-b>,
  "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/Delay/Examples.agda#L12",
)[
//typstfmt::off
```hs
comp-b : ∀ {i} -> Delay ℤ i
comp-b = later λ where .force -> now 0ℤ
```
//typstfmt::on
  ]
The term above represent the same converging computation, albeit in a different
number of steps. There are situations in which we want to consider equal
computations that result in the same outcome, be it a concrete value (or
failure) or a diverging computation. Of course, we cannot use Agda's
propositional equality, as the two terms _are not the same_:
#mycode(
  ref: <code-comp-a-eq-comp-b>,
  "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/Delay/Examples.agda#L15",
)[
//typstfmt::off
```hs
comp-a≡comp-b : comp-a ≡ comp-b
comp-a≡comp-b = refl
-- ^ now 0ℤ != later (λ { .force → now 0ℤ }) of type Delay ℤ ∞
```
//typstfmt::on
]

We thus define an equivalence relation on `Delay` which we call *weak
bisimilarity*. In words, weak bisimilarity relates two computations such that
either both diverge or both converge to the same value, independent of the
number of steps taken#footnote[ *Strong* bisimilarity, on the other hand,
requires both computation to converge to the same value in the same number of
steps; it is easy to show that strong bisimilarity implies weak bisimilarity.].
The definition we give in #thmref(<def-weak-bisimilarity>)[Definition] follows 
those given by 

#todo([Tell more about where this definition comes from])

#definition(
  name: "Weak bisimilarity",
)[
    Let $a_1$ and $a_2$ be two terms of type $A$. Then, weak bisimilarity of terms
    of type `Delay A` is defined by the following inference rules.

    #align(
      center,
      tablex(
        columns: 4,
        align: center + horizon,
        auto-vlines: false,
        auto-hlines: false,
        prooftrees.tree(
          prooftrees.axi(pad(bottom: 5pt, [$a_1 space eq.triple space a_2$])),
          prooftrees.uni[$"now" space a_1 space tilde.triple space "now" space a_2$],
        ),
        [$"now"$],
        prooftrees.tree(
          prooftrees.axi(pad(bottom: 5pt, [$"force" x_1 space tilde.triple space "force" x_2$])),
          prooftrees.couni[$"later" space x_1 space tilde.triple space "later" space x_2$],
        ),
        [$"later"$],
        prooftrees.tree(
          prooftrees.axi(pad(bottom: 5pt, [$"force" x_1 space tilde.triple space x_2$])),
          prooftrees.uni[$"later" space x_1 space tilde.triple space x_2$],
        ),
        [$"later"_l$],
        prooftrees.tree(
          prooftrees.axi(pad(bottom: 5pt, [$x_1 space tilde.triple space "force" x_2$])),
          prooftrees.uni[$x_1 space tilde.triple "later" space x_2$],
        ),
        [$"later"_r$],
      ),
    )
    <def-weak-bisimilarity>
  ]

The implementation in Agda of #thmref(<def-weak-bisimilarity>)[Definition]
follows the rules above but uses sized to deal with coinductive definitions (see
@subsection-agda-sized_types[Subsection]).
#mycode(
  ref: <code-weak-bisim>,
  "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/Delay/WeakBisimilarity/Core.agda#L16",
)[
//typstfmt::off
```hs
data WeakBisim {a b r} {A : Set a} {B : Set b} (R : A -> B -> Set r) i :
           (xs : Delay A ∞) (ys : Delay B ∞) -> Set (a ⊔ b ⊔ r) where
  now   : ∀ {x y} -> R x y -> WeakBisim R i (now x) (now y)
  later : ∀ {xs ys} -> Thunk^R (WeakBisim R) i xs ys
            -> WeakBisim R i (later xs) (later ys)
  laterₗ : ∀ {xs ys} -> WeakBisim R i (force xs) ys
            -> WeakBisim R i (later xs) ys
  laterᵣ : ∀ {xs ys} -> WeakBisim R i xs (force ys)
            -> WeakBisim R i xs (later ys)
```
//typstfmt::on
  ]
This definition also allows us to abstract over the relation between the values
of the parameter type $A$ and have a single definition for multiple kinds of
relations. Propositional equality is still the most frequently used relation, so
we define a special notation for this specialization:
#mycode(
  ref: <code-weak-bisim-propeq>,
  "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/Delay/WeakBisimilarity/Core.agda#L33",
)[
//typstfmt::off
```hs
infix 1 _⊢_≋_
_⊢_≋_ : ∀ i → Delay A ∞ → Delay A ∞ → Set ℓ
_⊢_≋_ = WeakBisim _≡_
```
//typstfmt::on
]

We also show that weak bisimilarity as we defined it is an equivalence relation.
When expressing this theorem in Agda, it is also necessary to make the relation
`R` we abstract over be an equivalence relation, as shown in
#thmref(<thm-weak-bisimilarity-equivalence>)[Theorem].

#theorem(
  name: "Weak bisimilarity is an equivalence relation",
)[
    #mycode(
      "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/Delay/WeakBisimilarity/Relation/Binary/Equivalence.agda",
      proof: <proof-weak-bisimilarity-equivalence>,
    )[
//typstfmt::off
```hs
reflexive : ∀ {i} (r-refl : Reflexive R)  -> Reflexive (WeakBisim R i)
symmetric : ∀ {i} (r-sym : Sym P Q) -> Sym (WeakBisim P i) (WeakBisim Q i)
transitive : ∀ {i} (r-trans : Trans P Q R)
              -> Trans (WeakBisim P i) (WeakBisim Q i) (WeakBisim R i)
```
//typstfmt::on
      ]
    <thm-weak-bisimilarity-equivalence>
  ]

#thmref(<thm-delay-monad>)[Theorem] affirms that `Delay` is a monad up to weak
bisimilarity.

#theorem(
  name: [`Delay` is a monad],
)[
    The triple (`Delay`, `now`, `bind`) is a monad and respects monad laws up to
    bisimilarity. In Agda:
    #mycode(
      "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/Delay/Examples.agda#L19",
      proof: <proof-delay-monad>,
    )[
//typstfmt::off
```hs
left-identity : ∀ {i} (x : A) (f : A -> Delay B i) -> (now x) >>= f ≡ f x
right-identity : ∀ {i} (x : Delay A ∞) -> i ⊢ x >>= now ≋ x
associativity : ∀ {i} {x : Delay A ∞} {f : A -> Delay B ∞}
  {g : B -> Delay C ∞} -> i ⊢ (x >>= f) >>= g ≋ x >>= λ y -> (f y >>= g)
```
//typstfmt::on
      ]
    <thm-delay-monad>
  ]

== Convergence, divergence and failure<section-convergence>
Now that we have a means to relate computations, we also want to define
propositions to characterize them. The `Delay` monads allows us to model the
effect of non-termination, but we also want to model the behaviour of program
that terminate but in a wrong way, which we name _failing_. We model this effect
with the aid of the `Maybe` monad, creating a new monad that combines the two
behaviours: we baptize this new monad `FailingDelay`. This monad does not have a
specific datatype (as it is the combination of two existing monads), so we
directly show the definition of `bind` in Agda (#coderef(<code-bind-fd>)).
#mycode(
ref: <code-bind-fd>,
"https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/FailingDelay/Effectful.agda#L31",
)[
//typstfmt::off
```hs
bind : ∀ {i} (d : Delay {ℓ} (Maybe A) i) (f : (A -> Delay {ℓ′} (Maybe B) i))
        -> Delay {ℓ′} (Maybe B) i
bind (now (just x)) f = f x
bind (now nothing) f = now nothing
bind (later x) f = later (λ where .force -> bind (x .force) f)
```
//typstfmt::on
]

Having a monad that deals with the three effects (if we consider convergence the
third) we want to model, we now define proposition for these three states. The
first we consider is termination (or convergence); in words, we define a program
to converge when there exists a term `v` such that the program is (weakly)
bisimilar to it (see #thmref(<def-converging-program>)[Definition]).

#definition(
  name: "Converging program",
)[
      #mycode(
         "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/FailingDelay/Relation/Binary/Convergence.agda#L21",
      )[
//typstfmt::off
```hs
_⇓_ : ∀ (x : Delay (Maybe A) ∞) (v : A) -> Set ℓ
x ⇓ v = ∞ ⊢ x ≋ (now (just v))

_⇓ : ∀ (x : Delay (Maybe A) ∞) -> Set ℓ
x ⇓ = ∃ λ v -> ∞ ⊢ x ≋ (now (just v))
```
//typstfmt::on
        ]
    <def-converging-program>
  ]
We then define a program to diverge when it is bisimilar to an infinite chain of
`later`, which we named `never` in #coderef(<code-never>) (see
#thmref(<def-diverging-program>)[Definition]).
#definition(
  name: "Diverging program",
)[      #mycode(
         "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/FailingDelay/Relation/Binary/Convergence.agda#L30",
      )[
//typstfmt::off
```hs
_⇑ : ∀ (x : Delay (Maybe A) ∞) -> Set ℓ
x ⇑ = ∞ ⊢ x ≋ never
```
//typstfmt::on
] <def-diverging-program>]
The third and last possibility is for a program to fail: such a program
converges but to no value (see #thmref(<def-failing-program>)[Definition]).
#definition(
  name: "Failing program",
)[      #mycode(
         "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/FailingDelay/Relation/Binary/Convergence.agda#L27",
      )[
//typstfmt::off
```hs
_↯ : ∀ (x : Delay (Maybe A) ∞) -> Set ℓ
x ↯ = ∞ ⊢ x ≋ now nothing
```
//typstfmt::on
] <def-failing-program>]
We can say that a program, in our semantics, cannot show any other kind of
behaviour, therefore theorem #thmref(<thm-exec>)[Theorem] seems clearly true; in
a constructive environment like Agda we can, however, only postulate it.
#theorem(
  )[
      #mycode(
         "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/FailingDelay/Relation/Binary/Convergence.agda#L83",
      )[
//typstfmt::off
```hs
 three-states : ∀ {a} {A : Set a} {x : Delay (Maybe A) ∞}
                  -> XOr (x ⇓) (XOr (x ⇑) (x ↯))
```
//typstfmt::off
] <thm-exec> ]
