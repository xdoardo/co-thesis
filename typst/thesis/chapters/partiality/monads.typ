#import "/includes.typ": *

== Monads<section-monads>
In 1989, computer scientist Eugenio Moggi published a paper @moggi-monads in
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
Without `bind`, `h` would be a match on the value of `x`: if `x` is `just v`
then do something, otherwise, if `x` is `nothing`, return `nothing`. 
The underlying idea of monads in the context of computer science, as explained
by Moggi in @moggi-monads, is to describe "notions of computations" that may
have consequences comparable to _side effects_ of imperative programming
languages in pure functional languages.

=== Formal definition<subsubsection-monad-formal_def>
We will now give a formal definition of what monads are. They're usually
understood in the context of category theory and in particular _Kleisli
triples_; here, we give a minimal definition inspired by @kohl-monads-cs.

#definition(name: "Monad")[
Let $A$, $B$ and $C$ be types. A monad $M$ is defined as the triple (`m` ,
`unit`, `_>>=_`) where `m` is a monadic constructor denoting some side-effect
or impure behaviour; `unit : A -> M A` represents the identity function and 
`_>>=_ : M A -> (A -> M B) -> M B` is used for monadic composition. 

The triple must satisfy the following laws. 
1. (*left identity*) For every `x : A` and `f : A -> M B`, `unit x >>= f` $eq.triple$ `f x`;
2. (*right identity*) For every `mx : M A`, `mx >>= unit` $eq.triple$ `mx`; and
3. (*associativity*) For every `mx : M A`, `f : A -> M B` and `g : B -> M C`, 
   
   `(mx >>= f) >>= g` $eq.triple$ `mx >>= (λ my -> f my >>= g)`
]

== The Delay monad<subsection-monad-delay_monad>
In 2005, computer scientist Venanzio Capretta introduced the `Delay` monad to
represent recursive (thus potentially infinite) computations in a coinductive
(and monadic) fashion @capretta-delay. As described in @abel-nbe, the `Delay`
type is used to represent computations whose result may be available with some
_delay_ or never be returned at all: the `Delay` type has two constructors;
one, `now`, contains the result of the computation. The second, `later`,
embodies one "step" of delay and, of course, an infinite (coinductive) sequence
of `later` indicates a non-terminating computation, practically making
non-termination (partiality) an effect, taking the perspective of 

In Agda, the `Delay` type is defined as follows (using _sizes_, see
@section-sized_types):
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
An important notion relating terms of `Delay` type is that of _bisimilarity_.
*Strong* bisimilarity relates diverging computations and computations that converge 
to the same value using the same number of steps @danielsson-operational-semantics;
the formal definition we give is from @chapman-delay-quotient, and is shown in 
#thmref(<def-strong-bisim>)[Definition]; properties of this relation are given in 
#thmref(<thm-strong-bisimilarity-equivalence>)[Theorem].

A less strict relation is *weak* bisimilarity: it equally relates diverging
terms (coinductively), but it also allows the relation between computations
that converge to the same value but in different number of steps. 

#definition(name : "Strong bisimilarity")[
 Let $A$ be a type for which there exists an equivalence relation $R_A$, and
 let $a_1$ and $a_2$ be two terms of type $A$. Furthermore, let $x_1$ and $x_1$
 be two delayed terms. Then, we define the strong bisimilarity relation $~_A$
 as 
 #align(center, 
  tablex(
    columns: 2,
    align: center + horizon,
    auto-vlines: false,
    auto-hlines: false,
   prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [$a_1 space R space a_2$])),
      prooftrees.uni[_≈-now_: $"now" space a_1 space ~_A space "now" space a_2$],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [$x_1 space ~_A space x_2$])),
      prooftrees.uni[_≈-later_: $"later" space x_1 space ~_A space "later" space x_2$],
    ),
  ))

In Agda: 
//typstfmt::off
```hs
data Bisim {a b r} {A : Set a} {B : Set b} (R : A → B → Set r) i :
           (xs : Delay A ∞) (ys : Delay B ∞) → Set (a ⊔ b ⊔ r) where
  now   : ∀ {x y} → R x y → Bisim R i (now x) (now y)
  later : ∀ {xs ys} → Thunk^R (Bisim R) i xs ys → Bisim R i (later xs) (later ys)

```
//typstfmt::on
<def-strong-bisim>
]

#theorem(name: "Strong bisimilarity is an equivalence relation")[
For every equivalence relation $A$, the strong bisimilarity relation $~_A$ is an equivalence relation.
Furthermore, strong bisimilarity is a transitive relation.
In Agda: 
//typstfmt::off
```hs
 reflexive : Reflexive R → ∀ {i} → Reflexive (Bisim R i)
 symmetric : Sym P Q → ∀ {i} → Sym (Bisim P i) (Bisim Q i)
 transitive : Trans P Q R → ∀ {i} → Trans (Bisim P i) (Bisim Q i) (Bisim R i)
```
//typstfmt::on
<thm-strong-bisimilarity-equivalence>
]


#definition(name : "Weak bisimilarity")[
 Let $A$ be a type for which there exists an equivalence relation $R_A$, and
 let $a_1$ and $a_2$ be two terms of type $A$. Furthermore, let $x_1$ and $x_1$
 be two delayed terms. Then, we define the weak bisimilarity relation $~_A$
 as 
 #align(center, 
  tablex(
    columns: 2,
    align: center + horizon,
    auto-vlines: false,
    auto-hlines: false,
   prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [$a_1 space R space a_2$])),
      prooftrees.uni[_≈-now_: $"now" space a_1 space ~_A space "now" space a_2$],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [$"force" x_1 space ~_A space "force" x_2$])),
      prooftrees.uni[_≈-later_: $"later" space x_1 space ~_A space "later" space x_2$],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [$"force" x_1 space ~_a space  x_2$])),
      prooftrees.uni[_≈-later-l_: $"later" space x_1 space ~_a space x_2$],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [$x_1 space ~_a space  "force" x_2$])),
      prooftrees.uni[_≈-later-r_: $x_1 space ~_a "later" space x_2$],
    ),
  )
)

In Agda: 
//typstfmt::off
```hs
data Bisim {a b r} {A : Set a} {B : Set b} (R : A -> B -> Set r) i :
           (xs : Delay A ∞) (ys : Delay B ∞) -> Set (a ⊔ b ⊔ r) where
  now   : ∀ {x y} -> R x y -> Bisim R i x y 
  later : ∀ {xs ys} -> Thunk^R (Bisim R) i xs ys -> Bisim R i (later xs) (later ys)
  laterₗ : ∀ {xs ys} -> Bisim R i (force xs) ys -> Bisim R i (later xs) ys
  laterᵣ : ∀ {xs ys} -> Bisim R i xs (force ys) -> Bisim R i xs (later ys)
```
//typstfmt::on
<def-weak-bisim>
]

#theorem(name: "Weak bisimilarity is an equivalence relation")[
For every equivalence relation $A$, the weak bisimilarity relation $~_A$ is an equivalence relation.
In Agda: 
//typstfmt::off
```hs
 reflexive : Reflexive R → ∀ {i} → Reflexive (WeakBisim R i)
 symmetric : Sym P Q → ∀ {i} → Sym (Bisim P i) (WeakBisim Q i)
```
//typstfmt::on
<thm-weak-bisimilarity-equivalence>
]
It's also trivial to show that strong bisimilarity implies weak bisimilarity.
We can also now prove monad laws up to strong bisimilarity, as shown in
#thmref(<thm-delay-monad>)[Theorem].

#theorem(name: [`Delay` is a monad])[
The triple (`Delay`, `now`, `bind`) is a monad and respects monad laws up to
bisimilarity. In Agda: 
//typstfmt::off
```hs
 left-identity : ∀ {i} (x : A) (f : A -> Delay B i) -> bind (now x) f ≡ f x
 right-identity : ∀ {i} (x : Delay A ∞) -> i ⊢ x >>= now ≈ x
 associativity : ∀ {i} {x : Delay A ∞} {f : A -> Delay B ∞} {g : B -> Delay C ∞} 
  -> i ⊢ (x >>= f) >>= g ≈ x >>= λ y -> (f y >>= g) 
```
//typstfmt::on
<thm-delay-monad>
]
