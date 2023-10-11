#import "/includes.typ": *

== Induction<section-recursive-induction>
The easiest and most intuitive inductive datatype is that of natural numbers. In
Agda, one may represent them as shown in @code-nat.
#code(label: <code-nat>)[
  ```hs
        data Nat : Set where
         zero : Nat
         succ : Nat -> Nat
        ```
]
A useful interpretation of inductive datatypes is to imagine concrete instances
as trees reflecting the structure of the constructors, as shown in
@fig-nat-tree; of course, this interpretation is not limited to _degenerate_
trees and it can be used to represent any kind of inductive structure such as
lists (which shall be binary trees), trees themselves and so on.
#figure(canvas({
  import draw: *

  tree.tree(
    ([zero], ([succ zero], ([succ succ zero], [...]))),
    spread: 2.5,
    grow: 1.5,
    draw-node: (node, _) => {
      circle((), radius: .45, stroke: none)
      content((), node.content)
    },
    draw-edge: (from, to, _) => {
      line(
        (a: from, number: .6, abs: true, b: to),
        (a: to, number: .6, abs: true, b: from),
        mark: (end: ">"),
      )
    },
    title: "tree",
  )
}), caption: "Structure of a natural number as tree of constructors")
<fig-nat-tree>
Our interest is not limited to the definition of inductive datatypes, we also
want to prove their properties: the correct mathematical tool to do so is the
_principle of induction_, which has been implicitly used, in history, since the
medieval times of the Islamic golden age, even if some works, such as
@acerbi-plato, claim that Plato's Parmenide contained implicit inductive proofs
already. Its modern version, paired with an explicit formal meaning, goes back
to the foundational works of Boole, De Morgan and Peano in the 19th century.

Suppose we want to prove a property $P$ of natural numbers. This property can
be, for example, @thm-powers[Theorem]. 
#theorem(label: <thm-powers>)[
For all natural numbers $n$, the sum of the first $n$ powers of $2$ is $2^n -1$,
or
#align(center, $forall n , sum_(i = 0)^(n-1) 2^i eq.triple 2^n - 1$)
]
For the sake of the explaination, we give a proof of @thm-powers in a
discursive manner, so that we are able to delve into each step. 

A proof by induction begins by proving a base case (typically $0$ or $1$, but
it is not necessarily always the case); we choose to prove it for $n = 0$: the
sum of the first $0$ powers of $2$ is $0$, and $2^0 -1 = 1 -1 = 0$, therefore
the case base is proved.

The power of the induction principle shows up here. The prover now assumes that
the principle holds for every number up to $n$ (this is called the _inductive
hypothesis_) and using this fact, which in this case is that $sum_(i = 0)^(n-1)
2^i = 2^n$, the prover shows that the statement holds for $n+1$ as well: 

#align(center, $sum_(i = 0)^n 2^i = sum_(i = 0)^(n-1) 2^i + 2^n = 2^n + 2^n - 1 = 2^(n+1) - 1$)

#linebreak()
The principle of induction is not limited to natural numbers. Every recursive
type has an _elimination principle_ which prescribes how to use terms of such
type that entails a *structural recursive definition* and a *principle of
structural induction*. This, in turn, implies that there exists a well-founded
relation inducing a well-order on the terms of the type: a well-founded
relation assures that, given a concrete instance of an inductive term,
analysing its constructor tree we will eventually reach a base case (`zero` in
the case of natural numbers, `nil` in the case of lists, the root node in case
of trees). Such a relation implies that a proof that examines a term in a
descending manner will eventually terminate.

There are many cases in which, however, we might want to express theorems about
structures that are not well-founded. A simple example of this is the following:
consider the infinite sequence of natural numbers

#align(center, [$s eq.def 0, 1, 2, 3, 4, ...$])

#linebreak()
The sequence $s$ certainly is a mathematical object that we can show theorems
about: for example, we might want to show that there is no element that is
greater than any other, but how are we to define such an object using
induction? An idea might be that of using lists as defined in @code-list.
#code(label: <code-list>)[
//typstfmt::off
```hs
data List (A : Set) : Set where
 []   : List A
 _::_ : A -> List A -> List A
```
//typstfmt::on
]
However, concrete terms which we can actually build up cannot be infinite; 
instead, they must be a finite sequence of applications of constructors. In
other words, the tree of constructors of a concrete list we can come up with is
necessarily of bounded (finite) height. 

We could try to trick Agda to define a potentially infinite sequence such as
$s$ as shown in @code-infinite-list. Then, we could represent $s$ as
`infinite-list 0`.
#code(label: <code-infinite-list>)[
//typstfmt::off
```hs
 infinite-list : Nat -> List Nat
 infinite-list n = n ∷ (infinite-list (n + 1))
-- Termination checking failed for the following functions:
--   infinite-list
-- Problematic calls:
--   infinite-list (n + 1)
--     (at /home/ecmm/t.agda:28,25-38)
```
//typstfmt::on
]
It turns out, however, that such a definition is not acceptable for Agda's
termination checker. One may argue that this is Agda's fault and that, for
example, Haskell may be completely fine with such a definition (and it is
indeed, as it employs a completely different strategy with regard to
termination checking). In the end, such a definition is indeed _recursive_.

== Coinduction<section-recursive-coinduction>
However, we must notice that a "fully constructed" infinite list such as $s$
does not have a base case and a possible inductive definition cannot be
well-founded. It turns out, then, that it is induction itself that can be
inadequate to reason about some infinite structures. It is important to remark,
however, that in general it is not problematic to reason about infinite
structures, and it is not infinity per sé that makes induction an inadequate
tool.

What induction does is build potentially infinite objects starting from
constructors. *Coinduction*, on the other hand, allows us to reason about
potentially infinite objects by describing how to observe (or destruct) them, as
opposed to how to build them. Following the previous analogy where inductive
datatypes were seen as constructor trees of finite height and functions or
inductive proofs operated on the nodes of this tree, we can see coinduction as a
means to operate on a tree of potentially infinite height by defining how to
extract data from each level of the tree.

While induction has an intuitive meaning and can be explained easily,
coinduction is arguably less intuitive and requires more background to grok
and, as anticipated in the introduction of this chapter, formal explainations
draw inspiration from various and etherogeneous fields of mathematics and
computer science. 

In this work we do not have the objective to give a formal and thorough
explaination of coinduction (which can be found, for example, in works such as
@sangiorgi-coinduction and @sangiorgi-advanced-coinduction); instead, we will
give a contained description of the relation between induction and coinduction,
then move to a more formal description using fixed points, with the only
objective of providing an intuition of what is the theoretical background
of coinduction.

Take again the example of lists as prescribed in @code-list. We can express
such a definition using inference rules as shown in @list-rules.

#figure(
tablex(columns: (auto, auto, auto, auto, auto),
align: horizon,
auto-lines: false,
        prooftrees.tree(
          prooftrees.axi(pad(bottom: 5pt, [$A : "Type"$])),
          prooftrees.uni[$"nil" : "List" A$],
        ),
        [_nil_],
        h(20pt),
        prooftrees.tree(
          prooftrees.axi(pad(bottom: 5pt, [$A : "Type"$])),
          prooftrees.axi(pad(bottom: 5pt, [$x s : "List" A$])),
          prooftrees.axi(pad(bottom: 5pt, [$x : A$])),
          prooftrees.nary(3)[$"cons" x space x s : "List" A$],
        ),
        [_cons_],
),
supplement: "Table",
caption: "Inference rules for the polymorphic List type"
)<list-rules>

This inference rules are _satisfied_ by some set of values. Suppose that the type 
$A$, interpreted as a _set_, is $A := {x, y, z}$; an example of a set satisfying 
the rules in @list-rules is

#linebreak()
#align(center, $S = {"nil", "cons" x "nil", "cons" y "nil", "cons" z "nil", "cons" x space ("cons" x "nil"), "cons" y space ("cons" x "nil"), ...}$)
#linebreak()
The set $S$ is exactly the inductive interpretation of the inference rules: in
$S$ there are those elements that follow the rules and those elements only.
Among all the sets that satisfy the rules, $S$ is the *smallest* one; however,
it is not the only possibility. We could take, for example, the *biggest* set
that follows that prescription and has every possible element of the universe
in it: of course, such a set, say $B$, also follows the inference rules in
@list-rules. The set $B$ is the coinductive interpretation of the inference
rules above. 

Consider now dropping the rule _nil_ from @list-rules. The set $S$, the
inductive interpretation, would be the empty set, as no base case is satisfied
and there is no "starting point" to build new lists. On the other hand the set
$B$ would still contain lots of lists, in particular infinite lists.


=== Induction and coinduction as fixed points<subsection-fixed-points>
The mathematical explaination is largely inspired by @pous-coinduction,
@pierce-types and @leroy-coinductive-bigstep and follows a "bottom-up" style of
exposition: we start with concepts that have no apparent connection with
(co-)induction, and reveal near the end how a specific interpretation of the
matter exposed can give an intuition of what coinduction is (as well as a
formal definition in a specific field of mathematics).

Let $U$ be a set such that there exists a binary relation $<= subset.eq U times
U$ that is reflexive, antisymmetric and transitive; we call $< U , <= >$ a
partially ordered set. Note that we concede the possibility for two elements of
$U$ to be incomparable without being the same. Formally:

#definition(
  name: "Partially ordered set",
  label: <def-poset>
)[
    Let $U$ be a set. $U$ is called a partially ordered set if there exists a
    relation $<= subset.eq U times U$
    such that for any $a, b, c in U$ $<=$ is
    1. *reflexive*: $a <= a$
    2. *antisymmetric*: $a <= b and b <= a => a = b$
    3. *transitive*: $a <= b and b <= c => a <= c$
    We call the pair $<U, <= >$ a partial order.
  ]

An example of a partially ordered set is the power set $2^X$ of any set $X$
with $<=$ being the usual notion of inclusion, as shown in @fig-poset-powerset.
This partially ordered set is in fact a *lattice* as it has a least element
(the empty set $emptyset$) and a greatest element (the entire set $U = {a, b,
c}$). Furthermore, the absence of paths between the sets ${a, b}$ and ${a, c}$
is an exemplification of the fact that two elements of $U$ may be incomparable.

#figure(
  render(width: 35%, "
   digraph mygraph {
   \"{a, b}\" -> \"{a, b, c}\"
   \"{a, c}\" -> \"{a, b, c}\"
   \"{b, c}\" -> \"{a, b, c}\"
   \"{b}\" -> \"{a, b}\"
   \"{a}\" -> \"{a, b}\"
   \"{a}\" -> \"{a, c}\"
   \"{c}\" -> \"{a, c}\"
   \"{b}\" -> \"{b, c}\"
   \"{c}\" -> \"{b, c}\"
   \"∅\" -> \"{a}\"
   \"∅\" -> \"{b}\"
   \"∅\" -> \"{c}\"
   }"),
  caption: [Hasse diagram for the partially ordered set created by the inclusion relation
    (represented by the arrows) on a set $U = {a, b, c}$],
)<fig-poset-powerset>

#definition(
  name: "Lattice",
  label: <def-lattice>
)[
    A lattice is a partial order $< U, <= >$ for which every pair of elements has a
    greatest lower bound and least upper bound, that is
    #align(
      center,
      $forall a in U, forall b in U, space exists s in U, exists i in U, space sup({a, b}) = s and inf({a, b}) = i$,
    )
    We also give a specific infix notation for the $"sup"$ and $"inf"$ when applied
    to binary sets:
    #align(
      center,
      [$a and b space eq.def space sup({a, b}) space $ and $space a or b space eq.def space inf({a,b})$],
    )
    which we name $"meet"$ and $"join"$, respectively.
  ]



Lattices are defined _complete_ if for every subset $L subset.eq U$ there are two
elements $"sup"(L)$ and $"inf"(L)$ such that the first is the smallest element
greater than or equal to all elements in $L$, while the second is the greatest
element less than or equal to all elements in $L$. Formally: 

#definition(
  name: "Complete lattice",
  label: <def-complete-lattice>
)[
    A complete lattice is a lattice for which every subset of the carrier set has a
    greatest lower bound and least upper bound, that is
    #align(
      center,
      $forall L subset.eq U, space exists s in U, exists i in U, space sup(L) = s and inf(L) = i$,
    )

    Complete lattices always have a bottom element
    #align(center, $bot eq.def inf(emptyset)$)
    and a top element
    #align(center, $top eq.def sup(U)$)
  ]

We also give a characterization of a specific kind of functions on $U$ in @def-monotone-on-lattice.
#definition(
  name: "Monotone function on complete lattices",
  label: <def-monotone-on-lattice>
)[
    Let $<U, <= >$ be a complete lattice. A function $f : U -> U$ is monotone if it
    preserves the partial order:
    #align(center, $forall a in U, forall b in U, space a <= b => f(a) <= f(b)$)
    We write $[U -> U]$ to denote the set of all monotone functions on $<U, <= >$.
]

#definition[
    Let $<U , <= >$ be a complete lattice; let $X$ be a subset of $U$ and let
    $f in [U -> U]$. Then we say that
    1. $X$ is $bold(f"-closed")$ if $f(X) subset.eq X$, that is, the output set is
      included in the input set;
    2. $X$ is $bold(f"-consistent")$ if $X subset.eq f(X)$, that is, the input set is
      included in the output set; and
    3. $X$ is a _fixed point_ of $f$ if $f(X) = X$.
  ]
For example (taken from @pierce-types), consider the following function on $U = {a, b, c}$:
#align(center, tablex(
  columns: 2,
  gutter: 4pt,
  align: center,
  auto-vlines: false,
  auto-hlines: false,
  [$e_1(emptyset) = {c}$],
  [$e_1({a,b}) = {c}$],
  [$e_1({a}) = {c}$],
  [$e_1({a,c}) = {b, c}$],
  [$e_1({b}) = {c}$],
  [$e_1({b,c}) = {a, b, c}$],
  [$e_1({c}) = {b, c}$],
  [$e_1({a, b, c}) = {a, b, c}$],
))
There is only one $e_1"-closed"$ set, ${a, b, c}$, and four $e_1"-consistent"$
sets, $emptyset, {c}, {b,c}, {a,b,c}$.

#theorem(
  name: "Knaster-Tarski",
  label: <thm-knaster-tarski>
)[
    Let $U$ be a complete lattice and let $f in [U -> U]$. The set of fixed points
    of $f$, which we define $"fix"(f)$, is a complete lattice itself. In particular
    1. the least fixed point of $f$ (noted $mu F$), which is the bottom element of $"fix"(f)$,
      is the intersection of all $f"-closed"$ sets.
    2. the greatest fixed point of $f$ (noted $nu F$), which is the top element of $"fix"(f)$,
      is the union of all $f"-consistent"$ sets.
  ]

#proof[ Omitted.#h(100%)]

From the example above, we have that $mu e_1 = nu e_1 = {a, b, c}$.
#corollary(label: <cor-ind-coind>)[
    1. *Principle of induction*: if $X$ is $f"-closed"$, then $mu f subset.eq X$;
    2. *Principle of coinduction*: if $X$ is $f"-consistent"$, then $X subset.eq nu f$.
    #h(100%)
]


Now that all the mathematical framework is in place, we can make a concrete
example. 

#figure(
tablex(columns: (auto, auto, auto, auto, auto),
align: horizon,
auto-lines: false,
        prooftrees.tree(
          prooftrees.axi([]),
          prooftrees.uni[$epsilon$],
        ),
        [_nil_],
        h(20pt),
        prooftrees.tree(
          prooftrees.axi(pad(bottom: 5pt, [$l$])),
          prooftrees.uni[$x :: l$],
        ),
        [_cons_],
),
supplement: "Table",
caption: "Inference rules for the untyped List type"
)<list-untyped-rules>

Consider the rules in @list-untyped-rules, a semplifications of rules in
@list-rules: we drop the polymorphism and leave implicit the part of the "is a
list" part of the judgment; we also consider $x$ in the cons rule to be any
element in the universe. We will show that we can build a complete lattice from
the rules in @list-untyped-rules and then show that the sets $S$ and $B$ that
we defined above are respectively the least fixed point and greatest fixed
point of a specific function $f$ on the complete lattice. We can interpret each
rule in @list-untyped-rules as an _inference system_ over a set $U$ of
judgements. In this case, we have 

#linebreak()
#align(center, $ U eq.def {j_1, j_2, j_3}$)
#linebreak()
where, for ease of exposure, we set $j_1 eq.def epsilon$, $j_2 eq.def l$ and $j_3 eq.def x :: l$.

The pair $<2^U, subset.eq>$ is a complete lattice, and has the structure
in @fig-lattice-U.

#figure(
  render(width: 35%, "
   digraph mygraph {
   \"{j₁, j₂}\" -> \"{j₁, j₂, j₃}\"
   \"{j₁, j₃}\" -> \"{j₁, j₂, j₃}\"
   \"{j₂, j₃}\" -> \"{j₁, j₂, j₃}\"
   \"{j₂}\" -> \"{j₁, j₂}\"
   \"{j₁}\" -> \"{j₁, j₂}\"
   \"{j₁}\" -> \"{j₁, j₃}\"
   \"{j₃}\" -> \"{j₁, j₃}\"
   \"{j₂}\" -> \"{j₂, j₃}\"
   \"{j₃}\" -> \"{j₂, j₃}\"
   \"∅\" -> \"{j₁}\"
   \"∅\" -> \"{j₂}\"
   \"∅\" -> \"{j₃}\"
   }"),
  caption: [Hasse diagram for the partially ordered set created by the inclusion relation
    (represented by the arrows) on the set $U = {j_1, j_2, j_3}$],
)<fig-lattice-U>

We now define another binary relation, $phi : 2^U times U$, that embodies the rules themselves: 
#linebreak()
#align(center, $ phi eq.def {(emptyset, j_1), (j_2, j_3)}$)
#linebreak()
Intuitively, if we have a rule $A/c$, then $(A , c) in phi$. We now define a
function $f : 2^U -> 2^U$ that represent a single step of derivation starting
from a set $S$ of premises using the rules in $phi$:
#linebreak()
#align(center, $ f(L) eq.def {j_1} union {c in U | exists A subset.eq L, (A, c) in phi}$)
#linebreak()

Going back to the expanded notation for rules#footnote[We do this as we
technically do not have $({j_1}, {j_3}) in phi$, although it is clearly
something expressed in the rules.] and adding a special notation for $x ::
epsilon eq.def [x]$, we have, for example,
#align(center, $f(emptyset) = {epsilon}$)
#align(center, $f({epsilon}) = {epsilon, [x]}$)
#align(center, $f({[x]}) = {epsilon, x :: [x]}$)
#align(center, $f({epsilon, [x]}) = {epsilon, [x], x :: [x]}$)
These sets are all $f$-consistents, as we always have $L subset.eq f(L)$.
Furthermore, the function $f$ is clearly monotone: $L subset.eq L'$ implies
that from $L'$ we will be able to derive at least the same conclusions that we
can derive from $L$, thus $f(L) subset.eq f(L')$. 

From @thm-knaster-tarski, we know that $f$ has a least fixed point and a
greatest fixed point, that is 

#align(center, $mu f = sect.big {L | f(L) subset.eq L}$)
#align(center, $nu f = union.big {L | L subset.eq f(L)}$)

The first set, the smallest $f$-closed is the set of terms that can be inductively generated from the rules, 
while the second set, the largest $f$-consistent is the set of terms that can be coinductively generated from the rules.
