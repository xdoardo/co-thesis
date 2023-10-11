#import "/includes.typ": *

== Recursion in Agda<section-recursion-agda>
We have already shown an example of inductive definition and proof by induction
in @section-recursive-induction[Section]. We continue our exposition of
inductive and coinductive datatypes and proofs, taking advantage of the effort
to introduce Agda and the practical infrastructure it provides to work with
inductive and coinductive proofs and definitions.

=== Termination<subsection-recursive-termination>
To this end, there are many aspects to take into account. The first is that in
Agda _"not all recursive functions are permitted - Agda accepts only these
recursive schemas that it can mechanically prove terminating"_ @agda-docs. It
is important to underline that this is a desired condition and not an
hindrance, as it is necessary to keep the consistency of the system, as we 
explained in @para-termination-consistency[Paragraph].

We inspect these aspects gradually as we define types and proofs by recursion.
The first datatype defined by recursion is that of natural numbers in
@code-nat. Of course, we can also define functions, as shown in @code-plus, and
define properties about such declarations leveraging the dependent type system of
Agda.

#code(label: <code-plus>)[
//typstfmt::off
```hs
_+_ : Nat -> Nat -> Nat
zero + n₂ =  n₂
suc n₁ + n₂ = suc (n₁ + n₂)
```
//typstfmt::on
]
#grid(columns: (auto, auto), column-gutter: 4pt,
[
#code(label: <code-thm-plus-zero-right-id>)[
//typstfmt::off
```hs
+-idᵣ  : ∀ (n : Nat) -> n + zero ≡ n
+-idᵣ zero = refl
+-idᵣ (suc n)
 rewrite (+-idᵣ n) = refl
```
//typstfmt::on
]],[
#code(label: <code-thm-plus-suc>)[
//typstfmt::off
```hs
+-sucᵣ : ∀ (n₁ n₂ : Nat)
  -> n₁ + suc n₂ ≡ suc (n₁ + n₂)
+-sucᵣ zero n₂ = refl
+-sucᵣ (suc n₁) n₂
 rewrite (+-sucᵣ n₁ n₂) = refl
```
//typstfmt::on
]])
#code(label: <code-plus-comm>)[
//typstfmt::off
```hs
+-comm : ∀ (n₁ n₂ : Nat) -> n₁ + n₂ ≡ n₂ + n₁
+-comm zero n₂ rewrite (+-idᵣ n₂) = refl
+-comm (suc n₁) n₂ rewrite (+-sucᵣ n₂ n₁) = cong suc (+-comm n₁ n₂)
```
//typstfmt::on
]
Although daunting at first, Agda is a very powerful system. In @code-plus-comm
we expressed the commutativity of the sum of naturals in a handful of lines: of
course, this is something that is well understood and fairly basic, but all the
infrastructure assures us that if the definition is accepted, there's no
possibility that our proof is wrong#footnote[Assuming there are no
inconsistencies in Agda itself.].
#grid(columns: (auto, auto), column-gutter: 4pt,
code(label: <code-monus>)[
//typstfmt::off
```hs
monus : Nat -> Nat -> Nat
monus zero _ = zero
monus (suc x) zero = suc x
monus (suc x) (suc y) = monus x y
```
//typstfmt::on
],code(label: <code-nonterm-div>)[
//typstfmt::off
```hs
div : Nat -> Nat -> Nat
div zero _ = zero
div (suc x) y = 
  suc (div (monus x y) y)
```
//typstfmt::on
])
However, even if Agda is "a powerful hammer", it comes with its limitations,
which we begin to investigate with the example of integer division. The
definition in @code-nonterm-div defines integer division as repeated
subtraction: it is acceptable to intuitively say that it is a terminating
definition, however Agda's termination checker does not agree and groans:
#align(center,[
```
Termination checking failed for the following functions: div
```
])
Agda's termination checker employs a syntactical analysis to prove the
termination of a definition; this means that each recursive call must follow a
strict schema: in practice, this means that the  only argument that are allowed
in recursive calls are immediate subexpressions or general (but strict)
subexpressions @agda-docs.

With this limitations, the checker is not able to capture relevant semantic
informations in our definition of `div` such as the fact that `monus` decreases
in the first parameter, thus making our definition of `div` unacceptable.

==== Sizes for induction<subsubsection-sizes-induction>
To overcome the limitations of syntactic termination checking, many authors
studied the possibility of using types themselves to allow a more powerful
termination checker. Abel, drawing from earlier works such as @pareto-sizes,
@uustalu-type-based-termination and @blanqui-type-based-termination, proposes
in @abel-miniagda a solution that involves a particular idea, _sizes_. We will
see that sizes have applications in coinductive definitions as well, but for
now we start by giving an intuition of what sizes are in the context of
inductive datatypes (such as natural numbers) and recursive functions (such as
`div`). 

In the inductive case, the sized approach is conceptually simple: we attach a
_size_ $i$ to every inductive type $D$ yielding a type $D^i$, and we check
that the size is diminishing in recursive calls @abel-miniagda. To give a
practical understanding of what sizes are, consider again @fig-nat-tree. Say
that $T$ is the tree representing the structure of a number $n$, where each
node is a constructor: a tree for $n$ will have $n+1$ nodes, thus the height of
the tree $T$ is $n+1$. In this context, we can understand the concept of size
as an upper bound on the height of the tree, therefore a valid size for the
tree $T$ (and for $n$) shall be any  size greater than or equal to $n+1$.

In Agda, sizes are represented as a built-in type `Size`. We will proceed in our
discussion gradually, and we start now by defining naturals with a notion of
size attached to them, as shown in @code-sized-nats. Agda, beyond the `Size` type, 
offers the user other primitives. One of these is the `↑ _` operator, which 
has type ```hs ↑ _ : Size -> Size``` and is used to compute the successor of a 
given size $i$; for any size $i$ it is $i < arrow.t i$.

#code(label: <code-sized-nats>)[
//typstfmt::off
```hs
data SizedNat : Size -> Set where
  zero : ∀ (i : Size) -> SizedNat (↑ i)
  succ : ∀ (i : Size) -> SizedNat (i) -> SizedNat (↑ i) 
```
//typstfmt::on
]
Let us examine the definition in @code-sized-nats in details. We define
`SizedNat` as a type indexed by `Size` with two constructors: `zero` and, as
expected, `succ`. As anticipated, we want sizes to be an _upper bound_ on the
height of the constructor tree, so it is natural that the constructor `zero`,
given any size $i$, constructs a tree with one node only (the constructor
`zero`) that has height $1$ and is upper bounded by $i + 1$ for any $i$; the
same applies to the constructor `succ`, that for any size $i$ and any other natural 
that has the upper-bounded height of $i$ builds a constructor tree with one node added 
(the `succ` constructor) that has height at most $i + 1$.

We consider now the example in @code-sized-monus, that sheds light on why sizes are an upper bound.
#code(label: <code-sized-monus>)[
//typstfmt::off
```hs
monus : ∀ (i : Size) (x : SizedNat i) (y : SizedNat ∞) -> SizedNat i
monus .(↑ i) (zero i) y = zero i
monus .(↑ i) (succ i x) (zero .∞) = succ i x 
monus .(↑ i) (succ i x) (succ .∞ y) = monus i x y
```
//typstfmt::on
] 

@code-sized-monus[Snippet] defines the usual _monus_ function, also noted as
$minus.dot$ in the literature and already shown (in an unsized version) in
@code-monus (this definition also uses _dot patterns_ -- see
@para-agda-dots[Paragraph]). 

The first thing to comment on is the size $infinity$, which indicates an upper
bound for terms whose height is unknown. In fact, in this case we don't know
what is the size of $y$: what we care about is that, intuitively, for any $x$
and $y$, it must be $x minus.dot y <= x$. Before, we could not express this
property of monus in a way that made it available to the termination checker
(which could then use it to prove termination): now, this property is
implicitly expressed in the type itself.

We can now define division of natural as repeated subtraction in a way that
satisfies Agda's termination checker, as shown in @code-sized-div.
#code(label: <code-sized-div>)[
//typstfmt::off
```hs
div : ∀ (i : Size) -> (x : SizedNat i) -> (y : SizedNat ∞) -> SizedNat i
div .(↑ i) (zero i) y = zero i
div .(↑ i) (succ i x) y = succ i (div i (monus i x y) y) 
```
//typstfmt::on
]

In all the examples we proposed we always made sizes explicit, however Agda's
termination checker and type system are mature enough to solve the system of
equations and find the correct sizes even if left implicit in the declaration
of functions.

// It is unclear to me what Agda does about subtyping of sized types, 
// so I won't talk about that here. 

=== Productivity<subsection-recursive-productivity>
We said, above, that termination of recursive definition is
necessary to keep consistency of the system. When it comes to coinduction and
corecursive definitions, another criterion, that of *productivity*, is
necessary. In short, productivity means that the corecursive function allows
new piece of the output to be visible in finite time @abel-eslli. Concretely, 
using a syntax criterion to enforce productivity, Agda requires that the definition 
of a corecursive function is such that every recursive call is immediately 
"under" a (co-)constructor.

The classical example of coinductive datatypes is that of _streams_, which in Agda 
is implemented as shown in @code-stream.
#code(label: <code-stream>)[
//typstfmt::off
```hs
record Stream (A : Set a) : Set a where
  coinductive
  constructor _∷_
  field
    head : A
    tail : Stream A
```
//typstfmt::on
]
This definition is a record paired with the `coindutive` keyword; we can thus
understand the fields `head` and `tail` as dual to constructors in inductive
definitions, embodying the observational nature of coinductive datatypes. We
believe that instead of trying to describe in details every choice of the
instrumentation for coinduction offered by Agda, it is better to show the
behaviour of the `Stream` datatype with an example. 
#code(label:<code-countFrom-stream>)[
//typstfmt::off
```hs
countFrom : Nat -> NatStream 
head (countFrom x) = x 
tail (countFrom x) = countFrom (x + 1)
```
//typstfmt::on
]
#code(label:<code-countFrom-at-1>)[
//typstfmt::off
```hs
countFrom-at-1 : head (tail (countFrom 0)) ≡ 1
countFrom-at-1 = refl
```
//typstfmt::on
]
In @code-countFrom-stream we already see the use of another technique offered by
Agda, that is _copatterns_, which, as explained in the documentation, _"[allow]
to define the fields of a record as separate declarations, in the same way that
we would give different cases for a function"_ @agda-docs, which where
originally thought as a tool in the context of coinductive definitions
@pientka-abel-copattern, then adapted to general usage.

The meaning of `countFrom` is given in the example `countFrom-at-1`
(@code-countFrom-at-1): the normalization of its type is 
//typstfmt::off
#align(center, `head (tail (countfrom 0)) => head (countFrom (0 + 1)) => 0 + 1 => 1`)
//typstfmt::on
and, in words, `countFrom` is an infinite stream starting at some number $n$
that for each observation - the application of a sequence of `tail`s followed
by a `head` - increments its value depending on the number of `tail` calls in
the observation; in other words, it is a representation of the infinite sequence 
of numbers $s$ we described earlier.

Coinduction, together with copatterns, allows us to write corecursive
definitions such as @code-repeat.
#code(label: <code-repeat>)[
//typstfmt::off
```hs
repeat : Nat -> NatStream
head (repeat x) = x 
tail (repeat x) = repeat x
```
//typstfmt::on
]
As before, not every definition is accepted, even if it may be conceptually
fine (in this case depending on what is `F`).
#code(label: <code-repeatF>)[
//typstfmt::off
```hs
repeatF : (NatStream -> NatStream) -> Nat -> NatStream
head (repeatF _ x) = x 
tail (repeatF F x) = F (repeatF F x)
```
//typstfmt::on
]
The function in @code-repeatF cannot be accepted, as the productivity checker
cannot make assumptions on what `F` does to the `NatStream` in input, and
groans again: 

``` Termination checking failed for the following functions: repeatF ```

==== Sizes for coinduction<subsubsection-sizes-coinduction>
The usefulness of sizes is not limited to prove recursive definitions
terminating, in fact, they can be used in the definition of coinductive types.

#agdacode(label: <code-agda-stream>, url: "https://agda.github.io/agda-stdlib/Codata.Sized.Stream.html#975")[
//typstfmt::off
```hs
data Stream (A : Set a) (i : Size) : Set a where
  _∷_ : A → Thunk (Stream A) i → Stream A i
```
//typstfmt::on
] 
We show, in @code-agda-stream, how Agda's standard library implements _sized_
streams at the time of writing; we shall examine it in details in order to
introduce all the concepts concerning the use of sizes in the (again, at the time
of writing) idiomatic way. The first thing to notice is that `Stream` is not a
`record` anymore and does not mention the coinductivity of the type: it is declared 
as an usual inductive datatype with a constructor `_::_` and is parameterized by 
a type `A` and a size `i`.

This constructor, which resembles the shape of the `cons` (or precisely
`_::_`) constructor of finite lists, takes a term of type `A` as its "head" and
a term of type `Thunk (Stream A) i` as its "tail". Of course, in order to
understand what this means it is necessary to inspect what `Thunk`s are.

#agdacode(label: <code-agda-thunk>, 
url:"https://agda.github.io/agda-stdlib/Codata.Sized.Thunk.html#482")[
//typstfmt::off
```hs
record Thunk {ℓ} (F : SizedSet ℓ) (i : Size) : Set ℓ where
  coinductive
  field force : {j : Size< i} → F j
```
//typstfmt::on
]
@code-agda-thunk[Snippet] shows the definition of `Thunk` as it is done in
Agda's standard library at the time of writing. 
#agdacode(label: <code-agda-sizedset>, url: "https://agda.github.io/agda-stdlib/Size.html#738")[
//typstfmt::off
```hs
SizedSet : (ℓ : Level) → Set (suc ℓ)
SizedSet ℓ = Size → Set ℓ
```
//typstfmt::on
]
`Thunk`s are parameterized by a level (see @para-agda-levels), a `SizedSet` `F`
of that level and a `Size`. `SizedSet`  is a type that characterizes, as it
suggests, the set that are paired with sizes, and its definition is shown in
@code-agda-sizedset. A `Thunk` has no constructor and only has a field `force`
that, given a size `j` of type `Size< i`, that is a size strictly less than
`i`, returns an instance of the type `F`.

In words, a `Thunk` is a way to abstract away the coinductive features of a
type, embodying its observational nature: taking the definition of the sized
`Stream` datatype using `Thunk`, we can define a stream as shown in
@code-agda-stream-repeat: to create the stream repeating the term `a`
indefinitely, we define it using the constructor `_::_`: the "head" is indeed
`a`, while the "tail" is an instance of a `Thunk` as prescribed by the anonymous λ
with a postfix projection of the `force` copattern. 

Excluded the aspect of tracking sizes, this methodology is exactly the same as
that used in eager languages to make computations lazy, simply delaying them
with a function call that is executed when needed.

#agdacode(label: <code-agda-stream-repeat>, url: "https://agda.github.io/agda-stdlib/Codata.Sized.Stream.html#1172")[
//typstfmt::off
```hs
repeat : A → Stream A i
repeat a = a ∷ λ where .force → repeat a
-- The same as 
-- repeat' : ∀ {i} (n : ℕ) -> Stream ℕ i
-- repeat' {i} n = n ∷ xs 
--  where 
--   xs : Thunk (Stream ℕ) i
--   force xs = repeat' n 
-- or, in postfix, xs .force = repeat' n
```
//typstfmt::on
]
@code-agda-stream[Snippet] shows the implementation of the `repeat` function as
done in Agda's standard library. We can compare this definition with that in
@code-repeat, which used copatterns. Copatterns are used in @code-agda-stream
as well, but are hidden in syntactic sugar and are not relative to the `Stream`
itself anymore but to `Thunk`, as explained above.

While for inductive types the size was an upper bound on the height of the
constructor tree of a term of that type, for coinductive types sizes represent
a lower bound on the _depth_ of the potentially infinite tree of
coconstructors. Each instance of a coinductive datatype will
always have arbitrary ($infinity$) size, but in order to provide 
well-formed definitions we reason with approximations, that is 
streams that have a depth $i$ for some arbitrary $i$ @abel-miniagda. 

Intuitively, the size of a coinductive datatypes gives a lower bound on the
number of times the term can be observed in a productive manner (that is,
yielding a result in finite time), it is therefore reasonable that `force`-ing
a `Thunk` (thus observing the next piece of the potentially infinite tree)
produces a result which has a size $j$ that is striclty smaller than the size
$i$ we started with.

#code(label: <code-repeatF-size>, placement: auto)[
//typstfmt::off
```hs
repeatF : ∀ {i} (n : ℕ) (F : ∀ {i} -> Stream ℕ i -> Stream ℕ i) 
            -> Stream ℕ i
repeatF {i} n F = n ∷ λ where .force {j} -> F {j} (repeatF n F)
```
//typsftm::on
]

When we tried to define the function in @code-repeatF, Agda's productivity
checker could not accept the definition because it was unaware of what the
function $F$ did to its input: was $F$ to observe parts of the stream in input,
was it to increase the stream adding coconstructors to its coconstructors
tree (thus increasing its then unknown size), or was it to leave the stream
untouched? We could not know. Now, with the help of sizes, we can impose
restrictions on $F$ such that we surely know that $F$ might increase the stream
or leave it untouched, but it can't make observations in such a way that leaves
the stream with less observations "available", as shown in @code-repeatF-size. 

=== Final considerations on sizes
Sizes give the programmer the ease to write recursive and corecursive functions
(thus, in a dependently typed environment such as Agda, also proofs) without
the troubles of syntactic termination and productivity checks.

Sizes, however, are not a complete solution to every problem: Agda's issues
page on GitHub, at the time of writing, includes $12$ issues where the use of
sizes makes Agda inconsistent; $7$ of these were solved, while $5$ are not and
one in particular, which allows a proof of $bot$, is marked as being put in the
_icebox_, that is, it is an _"Issue [that] there are no plans to fix for
upcoming releases."_ @agda-repo. 

#code(label: <agda-bottom>, placement: auto)[
//typstfmt::off
```hs
record T i : Set₁ where
  coinductive
  field force : (j : Size< i) → Set
open T

data Embed : ∀ i → T i → Set where
  abs : {A : T ∞} → A .force ∞ → Embed ∞ A

app : {A : T ∞} → Embed ∞ A → A .force ∞
app (abs x) = x

Fix′ : Size → (Set → Set) → Set
Fix′ i F = F (Embed i λ{ .force j → Fix′ j F})

data ⊥ : Set where

Omega : Set
Omega = Fix′ ∞ (λ A → A → ⊥)

self : Omega
self x = app x x

loop : ⊥
loop = self (abs self)
```
//typstfmt::on
]
There is no official statement regarding the future of sizes in Agda; however,
it seems that much effort is being put in the implementation of a _cubical_
version of Agda @vezzosi-cubical-agda, which draws inspiration from
@cohen-cubical and of course @hott-book.
