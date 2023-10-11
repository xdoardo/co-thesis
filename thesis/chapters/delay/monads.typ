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
combine computations. One of the most common instance of monad is the `Maybe`
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
// TODO label here to appropriate section
(where `{a}` is the _level_, see @subsection-agda-types[Subsection]) and two
functions representing its monadic features:
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
of reasoning for monads is exactly this, they are a tool used to model some
behaviour of the execution, which is also called *effect*. In the context of programming 
monads are also "computation builders".

Consider @code-monad-example: this example, even if simple, is a practical
application of the line of reasoning a programmer applies when using monads. In
this example, we want to simply increment an integer variable which might be,
for some reason, unavailable. The `_>>=_` function encapsulates the reasoning
that the programmer should make explicit, perhaps matching on the value of `x`,
in a compositional and reusable fashion.

#code(label:<code-monad-example>)[
//typstfmt::off
```hs
  h : Maybe ℕ → Maybe ℕ
  h x = x >>= λ v -> just (v + 1)
```
//typstfmt::on
]
The underlying idea of monads in the context of computer science, as explained
by Moggi in @moggi-monads, is to describe "notions of computations" that may
have consequences comparable to _side effects_ in pure functional languages.

=== Formal definition<subsubsection-monad-formal_def>
We will now give a formal definition of what monads are. They're usually
understood in the context of category theory and in particular _Kleisli
triples_; here, we give a minimal definition following @kohl-monads-cs.

#definition(
  name: "Monad",
  label: <def-monad>
)[
    Let $A$, $B$ and $C$ be types. A monad $M$ is defined as the triple (`M` ,
    `unit`, `_>>=_`) where `M` is a monadic constructor; `unit : A -> M A`
    represents the identity function and 
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

In Agda, the `Delay` type is defined as follows (using _sizes_ and
_levels_, see @subsubsection-sizes-coinduction[Subsection]):
#agdacode[
//typstfmt::off
```hs
data Delay {ℓ} (A : Set ℓ) (i : Size) : Set ℓ where
  now   : A → Delay A i
  later : Thunk (Delay A) i → Delay A i
```
//typstfmt::on
]
Paired with the following `bind` function (`return`,  or `unit`, is `now`).
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
as ```hs d .force```) in the `later` constructor. This is the only
possibile definition: for example,
//typstfmt::off
```hs bind' (later d) f = bind' (d .force) f```
//typstfmt::on
would not pass the termination and productivity checker; in fact, take the
`never` term as shown in @code-never: of course,
//typstfmt::off
```hs bind' never f```
//typstfmt::on
would never terminate.

#agdacode(label: <code-never>)[
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
  label: <code-comp-a>,
  "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/Delay/Examples.agda#L9",
)[
//typstfmt::off
```hs
comp-a : ∀ {i} -> Delay ℤ i
comp-a = now 0ℤ
```
//typstfmt::on
  ]
The term represents in @code-comp-a a computation converging to the value `0` immediately, as
no `later` appears in its definition.
#mycode(
  label: <code-comp-b>,
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
failure) or a diverging computation. We cannot use Agda's
propositional equality, as the two terms _are not the same_:
#mycode(
  label: <code-comp-a-eq-comp-b>,
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

We thus define an equivalence relation on `Delay` known as *weak
bisimilarity*. In words, weak bisimilarity relates two computations such that
either both diverge or both converge to the same value, independent of the
number of steps taken#footnote[ *Strong* bisimilarity, on the other hand,
requires both computation to converge to the same value in the same number of
steps; it is easy to show that strong bisimilarity implies weak bisimilarity.].


#definition(
  name: "Weak bisimilarity",
  label: <def-weak-bisimilarity>
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
  ]

The implementation in Agda of @def-weak-bisimilarity follows the rules above
but uses sizes to deal with coinductive definitions (see
@subsubsection-sizes-coinduction[Subsection]) and retraces the definition of _strong_
bisimilarity as implemented in Agda's standard library at the time of writing:
the difference with the rules shown in @def-weak-bisimilarity is that in the
latter the inference rules imply that propositional equality is the only kind
of relation allowed for two terms to be weakly bisimilar at the level of
non-delayed terms, while this definition allows terms of two potentially
different "end" types to be bisimilar as long as they are related by some
relation $R$. 

#mycode(
  label: <code-weak-bisim>,
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
Propositional equality is still the most frequently used
relation, so we define a special notation for this specialization, which
resembles that of the inference rules: 
#mycode(
  label: <code-weak-bisim-propeq>,
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

We also show that weak bisimilarity as we defined it is an equivalence
relation. When expressing this theorem in Agda, it is also necessary to make
the relation `R` we abstract over be an equivalence relation, as shown in
@thm-weak-bisimilarity-equivalence; as shown in
@danielsson-operational-semantics, the transitivity proof is not claimed to be
size preserving. 

#theorem(
  name: "Weak bisimilarity is an equivalence relation",
  label: <thm-weak-bisimilarity-equivalence>
)[
    #mycode(
      "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/Delay/WeakBisimilarity/Relation/Binary/Equivalence.agda",
      proof: <proof-weak-bisimilarity-equivalence>,
    )[
//typstfmt::off
```hs
reflexive : ∀ {i} (r-refl : Reflexive R)  -> Reflexive (WeakBisim R i)
symmetric : ∀ {i} (r-sym : Sym P Q) -> Sym (WeakBisim P i) (WeakBisim Q i)
transitive : ∀ {i} (r-trans : Trans P Q R) -> Trans (WeakBisim P ∞) (WeakBisim Q ∞) (WeakBisim R i)
```
//typstfmt::on
      ]
]

@thm-delay-monad states that `Delay` is a monad up to weak bisimilarity.

#theorem(
  name: [`Delay` is a monad],
  label: <thm-delay-monad>
)[
    The triple (`Delay`, `now`, `bind`) is a monad and respects monad laws up to
    weak bisimilarity. In Agda:
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
]]

== Convergence, divergence and failure<section-convergence>
Using the relation of weak bisimilarity, we want to define a characterization
of computations, which we will use later when expressing theorems regarding the
semantics of the language we will consider. 

The `Delay` monads allows us to model the effect of non-termination, but, other
than modeling converging computations, we also want to model the behaviour of
computations that terminate but in a wrong way, which we name _failing_. We
model this effect with the aid of the `Maybe` monad, creating a new monad that
combines the two behaviours: we baptize this new monad `FailingDelay`. 

This monad does not have a specific datatype (as it is the combination of two
existing monads), so we directly show the definition of `bind` in Agda
(@code-bind-fd).
#mycode(
label: <code-bind-fd>,
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

Having a monad that deals with the three effects (if we consider convergence
one) we want to model, we now define types for these three states. The
first we consider is termination (or convergence); in words, we define a
computation to converge when there exists a term `v` such that the computation
is (weakly) bisimilar to it (see @def-converging-computation).

#definition(
  name: "Converging computation",
  label: <def-converging-computation>
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
]]
We then define a computation to diverge when it is bisimilar to an infinite chain of
`later`, which we named `never` in @code-never (see
@def-diverging-computation).
#definition(
  name: "Diverging computation",
  label: <def-diverging-computation>
)[      #mycode(
         "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/FailingDelay/Relation/Binary/Convergence.agda#L30",
      )[
//typstfmt::off
```hs
_⇑ : ∀ (x : Delay (Maybe A) ∞) -> Set ℓ
x ⇑ = ∞ ⊢ x ≋ never
```
//typstfmt::on
]]
The third and last possibility is for a computation to fail: such a computation 
converges but to no value (see @def-failing-computation).
#definition(
  name: "Failing computation",
  label: <def-failing-computation>
)[      #mycode(
         "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Codata/Sized/FailingDelay/Relation/Binary/Convergence.agda#L27",
      )[
//typstfmt::off
```hs
_↯ : ∀ (x : Delay (Maybe A) ∞) -> Set ℓ
x ↯ = ∞ ⊢ x ≋ now nothing
```
//typstfmt::on
]]
We can already say that a computation, in the semantics we will define later,
will not show any other kind of behaviour, therefore @post-exec seems clearly
true; in a constructive environment like Agda we can, however, only postulate
it, as a proof would essentially be a solution to the halting problem. 
#postulate(
  label: <post-exec>
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
]]
