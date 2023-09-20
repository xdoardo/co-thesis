#import "/includes.typ": *

== Monads<section-monads>
In 1989, Eugenio Moggi published a paper @moggi-monads in
which the term _monad_, which was already used in the context of mathematics
and, in particular, category theory, was given meaning in the context of
functional programming. Explaining monads is, arguably, one the most discussed
topics in the pedagogy of computer science, and tons of articles, blog posts and
books try to explain the concept of monad in various ways.

A monad is a datatype equipped with (at least) two functions, `bind` (often
`_>>=_`) and `unit`; in general, we can see monads as a structure used to
combine computations. One of the most trivial instance of monad is the `Maybe`
monad, which we now present to investigate what monads are: in Agda,
the `Maybe` monad is composed of a datatype

#align(center, ```hs
data Maybe {a} (A : Set a) : Set a where
  just : A → Maybe A
  nothing : Maybe A
```)
and two functions representing its monadic features:

#align(center, ```hs
unit : A -> Maybe A
unit = just

_>>=_ : Maybe A → (A → Maybe B) → Maybe B
nothing >>= f = nothing
just a  >>= f = f a
```)

The `Maybe` monad is a structure that represents how to deal with computations
that may result in a value but may also result in nothing; in general, the line
of reasoning for monads is exactly this, they are a means to model a behaviour
of the execution, or *effects*: in fact, they're also called "computation builders" in the
context of programming. Let's give an example:
#align(center, ```hs
h : Maybe ℕ → Maybe ℕ
h x = x >>= λ v -> just (v + 1)
```)

The underlying idea of monads in the context of computer science, as explained
by Moggi in @moggi-monads, is to describe "notions of computations" that may
have consequences comparable to _side effects_ of imperative programming
languages in pure functional languages.

=== Formal definition<subsubsection-monad-formal_def>
We will now give a formal definition of what monads are. They're usually
understood in the context of category theory and in particular _Kleisli
triples_; here, we give a minimal definition inspired by @kohl-monads-cs.

#definition(name: "Monad")[
Let $A$, $B$ and $C$ be types. A monad $M$ is defined as the triple (`M` ,
`unit`, `_>>=_`) where `M` is a monadic constructor denoting some side-effect
or impure behaviour; `unit : A -> M A` represents the identity function and 
`_>>=_ : M A -> (A -> M B) -> M B` is used for monadic composition. 

The triple must satisfy the following laws. 
1. (*left identity*) For every `x : A` and `f : A -> M B`, `unit x >>= f` $eq.triple$ `f x`;
2. (*right identity*) For every `mx : M A`, `mx >>= unit` $eq.triple$ `mx`; and
3. (*associativity*) For every `mx : M A`, `f : A -> M B` and `g : B -> M C`, 
   
   `(mx >>= f) >>= g` $eq.triple$ `mx >>= (λ my -> f my >>= g)`
]

== The Delay monad<subsection-monad-delay_monad>
In 2005, Venanzio Capretta introduced the `Delay` monad to
represent recursive (thus potentially infinite) computations in a coinductive
(and monadic) fashion @capretta-delay. As described in @abel-nbe, the `Delay`
type is used to represent computations whose result may be available with some
_delay_ or never be returned at all: the `Delay` type has two constructors;
one, `now`, contains the result of the computation. The second, `later`,
embodies one "step" of delay and, of course, an infinite (coinductive) sequence
of `later` indicates a non-terminating computation, practically making
non-termination an effect.

In Agda, the `Delay` type is defined as follows (using _sizes_ and _levels_, see
@subsection-agda-sized_types[Subsection]):
#align(center, ```hs
data Delay {ℓ} (A : Set ℓ) (i : Size) : Set ℓ where
  now   : A → Delay A i
  later : Thunk (Delay A) i → Delay A i
```)
We equip with the following `bind` function:
#align(center, ```hs
 bind : ∀ {i} → Delay A i → (A → Delay B i) → Delay B i
 bind (now a)   f = f a
 bind (later d) f = later λ where .force → bind (d .force) f
```)
In words, what `bind` does, is this: given a `Delay A i` `x`, it checks whether
`x` contains an immediate result (i.e., `x ≡ now a`) and, if so, it applies the
function `f`; if, otherwise, `x` is a step of delay, (i.e., `x ≡ later d`),
`bind` delays the computation by wrapping the observation of `d` (represented
as ```hs d .force```) in the `later` constructor. Of course, this is the only
possibile definition: for example, ```hs bind' (later d) f = bind' (d .force) f``` 
would not pass the termination and productivity checker; in
fact, take the `never` term as shown in @code-never: of course, ```hs bind' never f``` 
would never terminate.

#figure(```hs
 never : ∀ {i} -> Delay A i
 never = later λ where .force -> never
```, 
caption: [Non-terminating term in the `Delay` monad]
)<code-never>

We might however argue that `bind` as well never terminates, in fact `never`
_never yields a value_ by definition; this is correct, but the two views on
non-termination are radically different. The detail is that `bind'` observes
the whole of `never` immediately, while `bind` leaves to the observer the job
of actually inspecting what the result of `bind x f` _is_, and this is the
utility of the `Delay` datatype and its monadic features. 

== Bisimilarity<subsection-monad-bisimilarity>
A computation, expressed in the delay monad, may look like this: 
#align(center, mycode[
```hs
 comp-a : ∀ {i} -> Delay ℤ i
 comp-a = now 0ℤ
```
])
This term represents a computation converging to the value `0` immediately, as no
`later`s appear in its definition.
#align(center, mycode[
```hs
 comp-b : ∀ {i} -> Delay ℤ i
 comp-b = later λ where .force -> now 0ℤ
```
])
The term above represent the same converging computation, albeit in a different
number of steps. There are situations in which we want to consider equal
computations that result in the same outcome, be it a concrete value (or
failure) or a diverging computation. Of course, Agda's propositional equality, as 
the two terms _are not the same_: 
#align(center, mycode[
```hs
 comp-a≡comp-b : comp-a ≡ comp-b 
 comp-a≡comp-b = refl
 -- ^ now 0ℤ != later (λ { .force → now 0ℤ }) of type Delay ℤ ∞
```])

We thus define an equivalence relation on `Delay` which we call *weak
bisimilarity*. In words, weak bisimilarity relates two computations such that
either both diverge or both converge to the same value, independent of the
number of steps taken#footnote[ *Strong* bisimilarity, on the other hand,
requires both computation to converge to the same value in the same number of
steps; it's easy to show that strong bisimilarity implies weak bisimilarity.].
The definition we give 

#definition(name: "Weak bisimilarity")[
 Let $a_1$ and $a_2$ be two terms of type $A$. Then, weak bisimilarity of terms
 of type `Delay A` is defined by the following inference rules.

 #align(center, 
  tablex(
    columns: 4,
    align: center + horizon,
    auto-vlines: false,
    auto-hlines: false,
   prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [$a_1 space eq.triple space a_2$])),
      prooftrees.uni[$"now" space a_1 space tilde.triple space "now" space a_2$],
    ),[$"now"$],
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [$"force" x_1 space tilde.triple space "force" x_2$])),
      prooftrees.uni(pad(bottom: 0pt, top: 0pt, left: 0pt, right: 0pt, [])),
      prooftrees.uni[$"later" space x_1 space tilde.triple space "later" space x_2$],
    ), [$"later"$],
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [$"force" x_1 space tilde.triple space  x_2$])),
      prooftrees.uni[$"later" space x_1 space tilde.triple space x_2$],
    ), [$"later"_l$],
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [$x_1 space tilde.triple space  "force" x_2$])),
      prooftrees.uni[$x_1 space tilde.triple "later" space x_2$],
    ),[$"later"_r$]
  ))
<def-weak-bisimilarity>
]

The implementation in Agda of #thmref(<def-weak-bisimilarity>)[Definition]
follows the rules above but uses sized to deal with coinductive definitions
(see @subsection-agda-sized_types[Subsection])
#align(center, mycode[
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
])
