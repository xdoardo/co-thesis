#import "/includes.typ": *
= Introduction<chapter-intro>

Our objective is to define an _operational semantics_ for an _imperative
language_ targeting an adequate _monad_ to model the desired _effects_ and
operate _transformations_ on program sources, all in a _dependently typed_
_proof assistant_. This work, in a nutshell, is a case study to analyse how all
these techniques work when put together.

In this section we will introduce some conventions used throughout the work
(@section-conventions[Section]). Then, we will explain what it means to define
the _semantics_ of a language and why such an effort is useful
(@section-semantics[Section]). We will then turn to a bird-eye view of Agda
(@section-agda[Section]), which is the tool we used to mechanize all the
definitions and proofs in the thesis. 

== Notational conventions<section-conventions>
==== Inference rules
We will make use of inference rules in the form 
#align(center, prooftrees.tree( prooftrees.axi[$A$], prooftrees.uni[c]))
where $A$ is the set of _antecedents_ and $c$ is the _conclusion_. Intuitively, such
a rule means that if the _judgments_ in $A$ are true, then $c$ is true. If $A =
emptyset$, the rule $emptyset/c$ identifies an axiom.

==== Code snippets
We will make great use of code snippets. Snippets coming from different 
sources are indentified by different colours. 
#agdacode[ `This code is from Agda's standard library` #linebreak() ]
#code[ `This code has no relevant source` #linebreak() ]
#mycode("")[ `This code is part of the thesis` #linebreak() ]

== Semantics <section-semantics>
Semantics, in general, is a tool that has the objective to assign meaning to
the execution of programs in a certain programming language. In the literature,
many formal model of semantics appear: _denotational semantics_, _operational
semantics_, _axiomatic semantics_, _action semantics_, _algebraic semantics_,
_functorial semantics_ and many more @winskel-semantics. 

We will explore *operational* semantics in particular. This formalism, which
appeared for the first time in the definition of the semantics of Algol 68; in
general, operational semantics express the meaning of a program in a way that
directly reflects the execution of the program in a reference system. The
formalism of operational semantics has multiple flavours itself. 

*Small step* operational semantics, introduced by Plotkin in
@plotkin-structural and also known as _structural_ (or _structured_)
operational semantics, is expressed inductively and, as the name suggests,
structurally, as a sequence of finite steps. For example, consider the language
composed of natural numbers $n$ and fully-parenthesized sums $e := (e_1 +
e_2)$, where the result of the computation (the _values_) are natural numbers
(the result of the sum). 

We can express the rules of the small-step semantics of our toy language in the
form of inference rules as shown in @sema-small-step-sums. Notice that the $+$
operator is _overloaded_, as it appears both as a function between expressions
of the language and natural numbers. In words, for example, term $((1 + 1) +
1)$ would step to $((2) + 1)$, then $(2 + 1)$ and finally $3$: 
#align(center, $((1 + 1) + 1) ->_("rule" 5) ((2) + 1) ->_("rule" 2) (2 + 1) ->_("rule" 5) 3$)

#figure(
  tablex(columns: (140pt, 20pt, 140pt , 20pt),
  auto-lines: false,
  align: horizon,
    prooftrees.tree(
      prooftrees.axi(pad(bottom:5pt, $e_1 -> e_1'$)),
      prooftrees.uni($(e_1 + e_2) -> (e_1' + e_2)$)
      ),
      [(1)],
    prooftrees.tree(
      prooftrees.axi(pad(bottom:5pt, $e_1 -> n_1$)),
      prooftrees.uni($(e_1 + e_2) -> (n_1 + e_2)$)
      ),
      [(2)],
    prooftrees.tree(
      prooftrees.axi(pad(bottom:5pt, $e_2 -> e_2'$)),
      prooftrees.uni($(n_1 + e_2) -> (n_1 + e_2')$)
      ),
      [(3)],
    prooftrees.tree(
      prooftrees.axi(pad(bottom:5pt, $e_2 -> n_2$)),
      prooftrees.uni($(n_1 + e_2) -> (n_1 + n_2)$)
      ),
      [(4)],
    colspanx(3)[#prooftrees.tree(
      prooftrees.axi(pad(bottom:5pt, $n_1 + n_2 eq.triple n$)),
      prooftrees.uni($(n_1 + n_2) -> n$)
      )],
    [(5)]
    ),
  supplement: "Semantics",
  caption: "Small-step rules for sums"
)<sema-small-step-sums>

*Big step* operational semantics, introduced by Kahn in @kahn-natural and also known as
_natural_ operational semantics, puts in relation the final result of the
evaluation of a program term and the term itself (without intermediate steps).
Taking again the previous example, we can express the big-step semantics of this 
language as shown in @sema-big-step-sums and the computation of $((1 + 1) + 1)$
expressed with such rules would be simply $((1 + 1) + 1)  => 3$.

#figure(
  tablex(columns: auto,
  auto-lines: false,
  align: horizon,
    prooftrees.tree(
      prooftrees.axi(pad(bottom:5pt, $e_1 => n_1$)),
      prooftrees.axi(pad(bottom:5pt, $e_2 => n_2$)),
      prooftrees.axi(pad(bottom:5pt, $n_1 + n_2 eq.triple n$)),
      prooftrees.nary(3)[$(e_1 + e_2) => n$]
      )),
  supplement: "Semantics",
  caption: "Big-step semantics for sums"
)<sema-big-step-sums>

The two semantics have different advantages and disadvantages. Leroy, in
@leroy-coinductive-bigstep, claims that small-step semantics is more expressive
and preferred for some objectives such as proving the soundness of a type
system, while big-step semantics is to be preferred for some other
ends, such as proving the correctness of program transformations. 

=== Program transformations <subsection-transformations>
Program transformations are the core of our work. A program transformation is
an operation that changes in some way an input program in some source language
in another program in a target language. Examples of program transformations
are the static analysis of the source code such as _constant folding_, _dead
code elimination_, _register allocation_, _liveness analysis_ and many more
@allen-catalogue. The kind of transformations just cited are _source to
source_, that is, the transformation is a function from the input language to a
program in the same language.

Another important example of program transformation are _compilers_ for which,
in general, we often take the correctness for granted: in this case the
transformation outputs, generally, a result in a different language, for
example assembly code for an input in the C language; this kind of
transformations, for which the output language is different from the input one,
are known as _source to target_.

Consider the LLVM compiler infrastructure @llvm: it is composed of hundreds of
thousands of lines of code and performs various transformations from its own
intermediate representation, starting with a translation of the program in SSA
form, continuing with tens of (optional) optimizing transformations and
concluding with a last translation into a target language. In principle, we do
not have a formal assurance -- a *proof* -- that no transformation ever changes
the meaning of the input program, and the user has to trust the programmers and
the community (altough efforts have been put to verify at least parts of LLVM:
@lean-llvm, @zhao-llvm, @zakowski-llvm).

Having a formal statement that proves that the transformations operated on a
program do not change the semantics of the source language is obviously a much
desired feature, and many efforts in the literature have been in this
direction. One of the most notable ones is CompCert @compcert, which has the
objective of providing a formalized backend for (almost all of) the ISO C
standard by providing a compiler where the majority of transformations (all, if
we do not consider lexical analysis and printing to ASM as transformations) are
either programmed in Caml or programmed and proved in Coq @coq. 

To this end, having a formal definition of the semantics of a language is the
first step to prove the correctness of the transformations operated on programs
in that language; in general, the idea is to prove that the transformation does
not change the result of the execution of the transformed program. This means
that the _observable_ behaviour of the program is not changed by the
transformations: for textbook examples, these behaviours are often the termination, 
non-termination or crash of the program when executed. In realistic languages, 
observable behaviours can be also inputs and outputs. 


It is clear how finding the suitable definition of the semantics for the job is
an important task but, as noted in @leroy-coinductive-bigstep and
@danielsson-operational-semantics, it can be fairly difficult. The reason for
this difficulty is that we ideally want a representation that is able to
capture every detail of the semantics of the program but also be lightweight
enough to allow proofs and definitions to be streamlined. 

As stated in @danielsson-operational-semantics, we could consider expressing
the semantics of a language as an inductive relation, either small-step or
big-step, showing how and when the evaluation of a program converges to a
result. With this mechanism, we either lose the explicit meaning of diverging
(non-terminating) and failing programs or we shall add new rules for both
diverging and failing programs, inducing a multiplication of rules that can be
unreasonable for large languages. 

Furthermore, a functional definition (an interpreter) of the semantics
expressed in this fashion should have type 
#align(center, [`eval(Program, Context) -> Fails or Diverges or Converges`])
But such an interpreter, clearly, is impossible to implement in a total
constructive language, as this amounts to solving the halting problem.

As suggested by Danielsson in @danielsson-operational-semantics, we explore the
implementation and use of a functional semantics targeting the
coinductively-defined `Delay` monad (which will be studied in details in later
chapters) to represent non-termination, failure and termination in a concise
fashion. In this way, the semantics is an interpreter and its type signature
does not imply that we have to solve the halting problem.

#linebreak()
Now that we have an intuition of what our goal is, we move to the explaination
of the tool we used, Agda.

== Agda <section-agda>
Agda is a programming language and a proof assistant. Its development goes back
to 1999 where a first version was written by Catarina Coquand @coquand-emacs;
in 2005 Ulf Norell worked on a redesign @norell-thesis, which laid the
foundations for what Agda is today. In this section, we begin introducting what
proof assistants are and what their objectives are, and after that we will
introduce specific details of Agda.

=== Proof assistants<subsection-proof-assistants>
This introduction to proof assistants follows @geuvers-history. As the name
suggests, a proof assistant has the role of providing aid to the user in the
context of _proofs_, so that a user can set up a mathematical theory, define
properties and do logical reasoning with them. A mathematical proof can in
principle be reduced to a sequence of small steps each of which can be verified
simply and irrefutably. The role of a proof is twofold: one is to _convince_
the reader that the statement the proof is about is correct, and the other is
to _explain_ why the statement is correct. 

A mechanzed tool can be helpful to verify that each small step in a proof is
correct, thus convince the reader that the whole proof is correct, and one role
of a proof assistant is exactly that: a _proof checker_. Of course, the proof
checker itself must be reliable and convincing: to this end, one may have an
independent description of the logic underlying the tool, that is the set of
axioms and inference rules (the _kernel_) that are implemented in the checker.
Also, the correctness of the checker itself can be verified as well, proving
that the checker can verify a theorem $phi$ if and only if $phi$ is derivable
from the independent kernel.

==== The Curry-Howard isomorphism<paragraph-curry-howard>
The relation between logic and computer science is deep and has a long history,
and a full account of the historical events that occurred in the literature is
not the objective of this work: we choose, instead, to report the fundamental
discoveries and inventions.
The work of Alonzo Church in the 1930s led to the invention of the λ-calculus,
a formal system able to express computations and functions, while later
extensions added a type system. Almost two decades after the inventions of Church,
Haskell Curry noticed that the rules forming types in the λ-calculus can be
seen as logical rules @curry-functionality; finally, William Howard realized in
@howard-formulae that intuitionistic natural deduction can be seen as a typed
variant of the λ-calculus. 

Intuitionistic (or constructive) logic, as intended in the
Brouwer–Heyting–Kolmogorov interpretation (see @heyting-intuitionism,
@kolmogorov-intuitionism, @troelstra-intuitionism), postulates that each proof
must contain a _witness_: for example, a proof of $P and Q$ is a pair $<a, b>$
where $a$ is a proof of $P$ and $b$ is a proof of $Q$; a proof of $P => Q$ is a
function $f$ that converts a proof of $P$ into a proof of $Q$ and so on: we can
see already here a connection between a formal interpretation of logic and the
usual type system and programming languages we use daily.

These ideas together led to the *Curry-Howard correspondence* (or Curry-Howard
isomorphism), which essentially says that a proposition is identified with the
type (which we can se as a collection) of all its proofs, and a type is
identified with the proposition there exists a term of that type (so that each
of its terms is in turn a proof of the corresponding proposition). This, in
concrete, leads to correspondence shown in @table-curry-howard. 

#figure(tablex(
  columns: (150pt, 150pt), 
  align: center + horizon, 
  header-rows : 1, 
  [*Logic*], [*Type Theory*],
  [proposition], [type], 
  [predicate], [dependent type], 
  [proof], [term/program],
  [true], [unit type], 
  [false], [empty type],
  [conjunction], [product type], 
  [disjunction], [sum type], 
  [implication], [function type], 
  [negation], [function type into empty type], 
  [universal quantification], [dependent product type], 
  [existential quantification], [dependent sum type],
  [equality], [identity type]
  ),
  placement: auto,
  supplement: "Table",
  caption:[Curry-Howard correspondence between logic and type theory]
)<table-curry-howard>

By the time the correspondence appeared formally, many advancements were
already available in the world of proof assistants: for example, the Automath
proof checker introduced by de Bruijn in 1967 @debruijn-automath included many
notions that reappeared later in the literature such as _dependent types_.

==== Martin-Löf type theory
In 1972, Per Martin-Löf extended the ideas in the Curry-Howard isomorphism
introducing a new _type theory_ known as intuitionistic type theory (or
constructive type theory or, simply, Martin-Löf type theory, MLTT). This theory
internalizes the concepts of intuitionistic (or constructive) logic as intended
in the Brouwer–Heyting–Kolmogorov interpretation. Many extensions and versions
have been proposed in the literature: the first version was shown to be
inconsistent by Girard, and later revision were made consistent (removing the
_impredicativity_ that caused the inconsisency) and introduced inductive and
universe types. Every flavour of MLTT has dependent types which, as shown in
@table-curry-howard, are used to build types that are equivalent to universal
and existential quantifiers in predicate logic.

MLTT introduced many concepts and it is, as of today, the backbone of many
proof assistants, but it is not the only type theory available. Another example
is the Calculus of Construction (and its variants) proposed by Coquand
@coquand-coc, which is the theory underlying the Coq proof assistant. 
Another is the more recent _homotopy type theory_ @hott-book.

==== Termination and consistency<para-termination-consistency>
The logical system on which the proof assistant lies must respect strict
constraints. Perhaps one the most important is that every term -- which, as
explained above, is also a proof -- must be provably terminating. This is
necessary to keep the consistency of the system itself and avoid proofs of
$bot$, the type that has no constructor and thus cannot, by definition, be
possibly built, which in turn means that it cannot be proven.

This reasoning is also important in a setting where types as well depend on
arbitrary terms: for example, what would be the type of a type depending on the
value of an infinite loop?

Allowing non-terminating terms and non-well-founded recursive definitions, a
proof of $bot$ can be immediate: for example, by defining a term $x := x + 1$
one can easily come up with a proof of $0 = 1$. This requirement (together with
the requirement of productivity for coinductive definitions, as we will see in
later chapters), is shared between any kind of proof assistant. We will examine
these concepts in more details in @chapter-recursive.

#linebreak()
We conclude this section introducing proof assistants describing where Agda
sits in relation to what we just discussed. Agda is a proof assistant and a
programming language (at the time of writing, it even compiles to Javascript)
based on a flavour of MLTT, where termination (and productivity) of definitions
is enforced for the reasons cited above. We proceed, now, describing in details
its inner workings, starting from a lightweight introduction to its syntax.

=== Syntax <subsection-agda-syntax>
//typstfmt::off
The first thing to highlight in relation to the syntax of Agda is that every
character including unicode codepoints and "," is a valid identifier, except
"(" and ")". The character "\_"/* _ __**/ has a special meaning and allows the
definition of mixfix operators which can be used in multiple ways, as shown in
@code-mixfix. For example, `3::2::1::[]` is lexed as an identifier, and we must
use spaces to make Agda parse it as we may intend it (a list). These
are both valid identifiers as well `this+is*a-valid[identifier]`, `this,aswell`.
//typstfmt::on

#code(label: <code-mixfix>)[
//typstfmt::off
```hs
(if_then_else_) x y z
if x then y else z
(if x then_else_) y z
(if_then y else z) x
(if x then _ else z) y
```
//typstfmt::on
]

=== Type system <subsection-agda-types>
As anticipated, Agda is based on a flavour of Martin-Löf type theory and as
every MLTT it has dependent types. As explained above, this allows the user to
embed semantic informations about the programs at the type level and represent
logical statements in a computer program. In this subsection, we briefly
describe how types can be defined in Agda.


==== Data types <para-data>
One of the simplest datatypes is that of Boolean values. Agda's standard library 
defines them as shown in @code-bool.
#agdacode(url: "https://agda.github.io/agda-stdlib/Agda.Builtin.Bool.html#156", label: <code-bool>)[
//typstfmt::off
```hs
data Bool : Set where
  false : Bool
  true : Bool

```
//typstfmt::on
]
The `data` keyword is used to introduce new datatypes in the program. The type
system allows for more complex definitions, as prescribed by the logical system
it is based on. For example, we can define polymorphic lists as follows: 
#code(label: <code-list-nounipoly>)[
//typstfmt::off
```hs
data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) -> List A
```
//typstfm::on
]

In this example, where the `List` type is parameterized by the type `A`, we can
already see a glimpse of the power of Agda's type system, which will also be
explored in more depth when examining the definition of functions. 

==== Levels<para-agda-levels>
The fundamental type in Agda is `Set`, which we used in the previous examples
without giving a detailed description. `Set` is the sort of _small_ types
@agda-docs, but not every type in Agda is a `Set`, however; to avoid paradoxes
similar to that of Russel, Agda uses universe levels and provides an infinite
number of them. 

We thus have that `Set` is not of type `Set`, instead it is `Set : Set₁` and,
in turn, it is `Set₁ : Set₂, ... : Setₙ`, where the subscript `n` is its
*level*. In principle, we have that `Set` is implicitly `Set 0`. A type whose
elements are types themselves is called a _sort_ or _universe_ @agda-docs.  

It is interesting to underline that Agda's type system allows _universe polymorphism_, 
allowing the user to parameterize or index definitions on the unverse level as well, 
as shown in @code-stdlist.
#agdacode(url: "https://agda.github.io/agda-stdlib/Agda.Builtin.List.html#130", label: <code-stdlist>)[
//typstfmt::off
```hs
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) -> List A
```
//typstfm::on
]


==== Records<para-agda-records>
Another example of instrumentation Agda proposes to define datatypes are
*records*. From Agda's documentation: _"Records are types for grouping values
together. They generalise the dependent product type by providing named fields
and (optional) further components."_ @agda-docs. 

#code(label: <code-pair>)[
//typstfmt::off
```hs
record Pair {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    fst : A
    snd : B
```
//typstfmt::on
]

An example of record is shown in @code-pair, defining the type for pairs with
type polymorphism and universe polymorphism. This definition automatically
inserts in scope three new functions: one to create a `Pair` and two to access
its fields: we will examine this briefly, after having introduced the concept
of _functions_ in Agda.

=== Functions <agda-functions>
From the syntactic point of view function definitions are syntactically similar
to those in Haskell, following an equational style defining _clauses_. The
similarity with Haskell stops here, as typing rules in Agda are not similar to
those in Haskell, which uses a completely different type system.
#grid(columns: 2,
column-gutter: 10pt,
code(label: <code-not>)[
//typstfmt::off
```hs
not : Bool -> Bool
not false = true
not true = false
```
//typstfmt::on
], 

code(label: <code-id>)[
//typstfmt::off
```hs
id : ∀ {A : Set} -> A -> A
id a = a
```
//typstfmt::on
])

By the Curry-Howard isomorphism, types are univocally related to propositions
and function definitions are univocally linked to proofs. We can see this in
@code-id where, in code, we define a polymorphic function that for any
parameter $A$ outputs a result of type $A$; its definition is just returning
the parameter. We can interpret this in logic as follows: 
`∀ {A : Set} -> A -> A` 
_is_ the proposition $forall A : "Set", A => A$, while `id a = a` _is_ the
proof, in $lambda$-calculus, $lambda x . x$.

We now explore in more depth the use of Agda as a proof assistant. A part of
the usefulness of Agda is its interaction with the user through _holes_, which
indicate a term that the programmer does not have (conceptually) available yet;
Agda aids the programmer showing graphically the type of the hole: we
demonstrate both this aspect and the capacities of Agda in the definition of
proofs with an example. 

Suppose we want to encode in Agda the following logical statement:
#align(center, $forall b : "Bool", b or "false" eq.triple "false"$)
In Agda, we can represent this statement as follows: 
#code[
//typstfmt::off
```hs
∨-identityʳ : ∀ (b : Bool) -> b ∨ false ≡ b
∨-identityʳ false = refl
∨-identityʳ true = refl
```
//typstfmt::on
]

The previous example also shows _the proof_ for the statement: with pattern
matching on the value of `b` we can prove this simply by using the reflexivity
of the built-in propositional equality. To give a slightly more involved example 
to show other uses of Agda we define the function in @code-list-append that appends two `List`s
(see the definition of `List`s in @code-list-nounipoly).

#agdacode(url: "https://agda.github.io/agda-stdlib/Data.List.Base.html#1950", label: <code-list-append>)[
//typstfmt::off
```hs
_++_ : List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
```
//typstfmt::on
]
Suppose, now, that we want to prove the following statement: 

#linebreak()
#align(center, $forall l : "List", [] "++" l eq.triple l$)
#linebreak()
that is, that the empty list `[]` is the (right) identity of the append
operator. In Agda: 
#code(label:<code-list-append-identity>)[
//typstfmt::off
```hs
++-identityʳ : ∀ {A : Set} (l : List A) -> l ++ [] ≡ l
++-identityʳ [] = refl
++-identityʳ (x ∷ l) rewrite (++-identityʳ l) = refl
```
//typstfmt::on
]

@code-list-append-identity[Snippet] shows the use of another tool offered by
Agda: the `rewrite`. This keyword allows the programmer to extend Agda's
evaluation relation with new computation rules @agda-docs. In practice, this means that 
given an evidence that $x eq.triple y$, `rewrite` rules allow to change evidences involving 
$y$ to evidences using $x$. Consider the previous example: we had to prove that 
`(x ∷ l) ++ [] ≡ x ∷ l`. By the definition of `_++_` in @code-list-append, the term 
`(x ∷ l) ++ [] ` is _normalized_ to `x ∷ (l ++ [])`, which means that we must show 

#align(center, ``` x ∷ (l ++ []) ≡ x ∷ l```)

Instructing Agda to rewrite `++-identityʳ l`, which is a proof of `l ++ [] ≡ l`, 
means syntactically changing the occurrences of `l ++ []` with occurrences of
`l`, which leaves us to prove that `x ∷ l ≡ x ∷ l`, which is easily done by
reflexivity.

==== Copatterns
Going back to the example shown in @code-pair, the record definition
automatically defines a constructor 
#align(center, [`Pair : ∀ {a b} (A : Set a) (B : Set b) -> Set (a ⊔ b)`])
and two projection functions
#align(center, [`Pair.fst : ∀ {a b} {A : Set a} {B : Set b} -> Pair A B -> A`])
#align(center, [`Pair.snd : ∀ {a b} {A : Set a} {B : Set b} -> Pair A B -> B`])
#linebreak()
Elements of `Pair` can be constructed using the extended notation or using
_copatterns_, as shown in @code-pair-copattern.
//typstfmt::on
#code(label: <code-pair-copattern>)[
//typstfmt::off
```hs
-- Extended notation  
p34 : Pair ℕ ℕ 
p34 = record {fst = 3; snd = 4} 
--
-- Copatterns 
-- Prefix notation
p34 : Pair ℕ ℕ 
Pair.fst p34 = 3
Pair.snd p34 = 4
-- Postfix notation
p34 : Pair ℕ ℕ 
p34 .Pair.fst  = 3
p34 .Pair.snd  = 4
```
//typstfmt::on
]


==== Dot patterns<para-agda-dots>
A dot pattern (also called inaccessible pattern) can be used when the only
type-correct value of the argument is determined by the patterns given for the
other arguments. A dot pattern is not matched against to determine the result
of a function call. Instead it serves as checked documentation of the only
possible value at the respective position, as determined by the other patterns.
The syntax for a dot pattern is `.t`.

As an example, consider the datatype `Square` defined as follows

#code[
//typstfmt::off
```hs
data Square : ℕ -> Set where
  sq : (m : ℕ) -> Square (m * m)
```
//typstfmt::on
]
Suppose we want to define a function `root : (n : ℕ) -> Square n -> ℕ` that
takes as its arguments a number n and a proof that it is a square, and returns
the square root of that number. We can do so as follows:
#code[
//typstfmt::off
```hs
root : (n : ℕ) -> Square n -> ℕ
root .(m * m) (sq m) = m
```
//typstfmt::on
]
