== Monads<section-monads>
In 1989, computer scientist Eugenio Moggi published a paper @moggi-monads in
which the term _monad_, which was already used in the context of mathematics,
and, in particular, category theory, was given meaning in the context of
functional programming. Explaining monads is, arguably, one the most discussed
topics in the pedagogy of computer science, and tons of articles, blog posts and
books try to explain the concept of monad in various ways, spacing from
high-level category theory to burritos @monads-burritos.

A monad is a datatype equipped with (at least) two functions, `bind` (often
`_>>=_`) and `unit`. In general, we can see monads as a structure used to
combine computations. One of the most trivial instance of monad is the `Maybe`
monad. Let's investigate what monads are by delving into this example: in Agda,
the `Maybe` monad is composed of a datatype

#align(center, ```hs
data Maybe {a} (A : Set a) : Set a where
  just : A → Maybe A
  nothing : Maybe A
```)
and two functions

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
of the execution (in fact, they're also called "computation builders" in the
context of programming). To explain this behaviour, let's give an example:
#align(center, ```hs
h : Maybe ℕ → Maybe ℕ
h x = x >>= λ v -> just (v + 1)
```)
Without `bind`, `h` would be a match on the value of `x`: if `x` is `just v`
then do something, otherwise, if `x` is `nothing`, return `nothing`. This
reflection shines a light on the behaviour of monads, as explained before: they
are a way to hide details of a computation.

== The Delay monad<subsection-monad-delay_monad>
In 2005, computer scientist Venanzio Capretta introduced the `Delay` monad to
represent recursive (thus potentially infinite) computations in a coinductive
(and monadic) fashion @capretta-delay. As described in @abel-nbe, the `Delay`
type is used to represent computations whose result may be available with some
_delay_ or never be returned at all: the `Delay` type has two constructors; one,
`now`, contains the result of the computation. The second, `later`, embodies one "step"
of delay and, of course, an infinite (coinductive) sequence of `later` indicates
a non-terminating computation.

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

