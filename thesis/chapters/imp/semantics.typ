#import "@preview/prooftrees:0.1.0"
#import "/includes.typ": *

== Semantics <imp-semantics>
Having understood the concrete and abstract syntax of Imp, we can move to the
meaning of Imp programs. We'll explore the operational semantics of the language
using the formalism of inference rules, then we'll show the implementation of
the semantics (as an intepreter) for these rules.

Before describing the rules of the semantics, we will give a brief explaination
of what we expect to be the result of the evaluation of an Imp program. As shown
in @imp-syntax-rules, Imp programs are composed of three entities: arithmetic
expression, boolean expression and commands.

#figure(```if true then skip else 1 ```, caption: "A simple Imp
program")<code-imp-simple-program> An example of Imp program is shown in
@code-imp-simple-program: note that is technically not well-typed, but we don't
care about this now. In general, we can expect the evaluation of an Imp program
to terminate in some kind value or diverge, but it might also *fail*: this is
the case when an uninitialized variable is used, as we mentioned in
@subsection-imp-introduction-syntax.

We could model other kinds of failures, both deriving from static analysis (such
as failures of type-checking) or from the dynamic execution of the program, but
we chose to model this kind of behaviour only: an example of this can be seen in
@code-imp-simple-failing.

#figure(```
while true do x := y
```, caption: "A failing (not diverging!) Imp program")
<code-imp-simple-failing>

We can now introduce the formal notation we will use to describe the semantics
of Imp programs. We already introduced the concept of store, which keeps track
of the mutation of identifiers and their value during the execution of the
program. We write #conv([c, $sigma$], $sigma_1$) to mean that the program $c$,
when evaluated starting from the context $sigma$, converges to the store $sigma_1$.

We write #fails([c, $sigma$]) to say that the program $c$, when evaluated in
context $sigma$, does not converge to a result but, instead, execution gets
stuck (that is, an unknown identifier is used).

The last possibility is for the execution to diverge, #div([c, $sigma$]): this
means that the evaluation of the program never stops and while no state of
failure is reached no result is ever produced. An example of this behaviour is
seen when evaluating @code-imp-simple-diverging.

#figure(```
while true do skip
```, caption: "A diverging Imp program")
<code-imp-simple-diverging>

We're now able to give inference rules for each construct of the Imp language:
we'll start from simple ones, that is arithmetic and boolean expressions, and
we'll then move to commands.

=== Arithmetic expressions <imp-semantics-arithmetic_expressions>
Arithmetic expressions in Imp can be of three kinds: integer ($ZZ$) constants,
identifiers and sums. As anticipated, the evaluation of arithmetic expressions
can fail, that is, the evaluation of arithmetic expression, conceptually, is not
a total function. Again, the possibile erroneous states we can get into when
evaluating an arithmetic expression mainly concerns the use of undeclared
identifiers and, as we did for stores, we can target the Maybe monad.

Without introducing them, we will use notations similar to that used earlier for
commands (#conv($dot.c$, $dot.c$) and #fails($dot.c$))
#figure(
  grid(
    columns: (1fr, 1fr, 1fr),
    rows: (40pt, 40pt),
    prooftrees.tree(prooftrees.axi[], prooftrees.uni[#conv([const n], [just n])]),
    prooftrees.tree(
      prooftrees.axi[$id in sigma$],
      prooftrees.uni[#conv([var id], [$sigma id$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#conv([$a_1$], [just $n_1$])])),
      prooftrees.axi(pad(bottom: 2pt, [#conv([$a_2$], [just $n_2$])])),
      prooftrees.nary(2)[#conv([$"plus" a_1 a_2$], [just $(n_1 + n_2)$])],
    ),
    prooftrees.tree(prooftrees.axi[$id in.not sigma$], prooftrees.uni[#fails([var id])]),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#fails([$a_1$])])),
      prooftrees.uni[#fails([$"plus" a_1 a_2$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#conv([$a_1$], [just $n_1$])])),
      prooftrees.axi(pad(bottom: 2pt, [#fails([$a_2$])])),
      prooftrees.nary(2)[#fails([$"plus" a_1 a_2$])],
    ),
  ),
  caption: "Inference rules for the semantics of arithmetic expressions of Imp",
  supplement: "Table",
)<imp-arith-semantics>

In Agda, these rules are implemented as shown in @code-aeval.

#figure(
  ```hs
  aeval : ∀ (a : AExp) (s : Store) -> Maybe ℤ
  aeval (const x) s = just x
  aeval (var x) s = s x
  aeval (plus a a₁) s = aeval a s >>= λ v₁ -> aeval a₁ s >>= λ v₂ -> just (v₁ + v₂)
  ```,
  caption: "Agda interpreter for arithmetic expressions",
)<code-aeval>

=== Boolean expressions <imp-semantics-boolean_expressions>
Boolean expressions in Imp can be of four kinds: boolean constants, negation of
a boolean expression, logical $and$ and, finally, comparison of arithmetic
expressions. The line of reasoning for the definition of semantic rules follows
what we underlined earlier, that is, we again target the Maybe monad.

#figure(
  grid(
    columns: (1fr, 1fr, 1fr),
    rows: (40pt, 40pt, 40pt),
    prooftrees.tree(prooftrees.axi[], prooftrees.uni[#conv([const c], [just c])]),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#conv([b], [c])])),
      prooftrees.uni[#conv([$not b$], [$not c$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#conv([$a_1$], [just $n_1$])])),
      prooftrees.axi(pad(bottom: 2pt, [#conv([$a_2$], [just $n_2$])])),
      prooftrees.nary(2)[#conv([le $a_1$ $a_2$], [just $(n_1 < n_2)$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#conv([$b_1$], [just $c_1$])])),
      prooftrees.axi(pad(bottom: 2pt, [#conv([$b_2$], [just $c_2$])])),
      prooftrees.nary(2)[#conv([and $b_1$ $b_2$], [just $(c_1 and c_2)$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#fails([b])])),
      prooftrees.uni[#fails([$not b$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#fails([$a_1$])])),
      prooftrees.uni[#fails([le $a_1$ $a_2$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#conv([$a_1$], [just $n_1$])])),
      prooftrees.axi(pad(bottom: 2pt, [#fails([$a_2$])])),
      prooftrees.nary(2)[#fails([le $a_1$ $a_2$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#fails([$b_1$])])),
      prooftrees.uni[#fails([and $b_1$ $b_2$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#conv([$b_1$], [just $c_1$])])),
      prooftrees.axi(pad(bottom: 2pt, [#fails([$b_2$])])),
      prooftrees.nary(2)[#fails([and $b_1$ $b_2$])],
    ),
  ),
  caption: "Inference rules for the semantics of boolean expressions of Imp",
  supplement: "Table",
)<imp-bool-semantics>

In Agda, these rules are implemented as shown in @code-beval.

#figure(
  ```hs
  beval : ∀ (b : BExp) (s : Store) -> Maybe Bool
  beval (const c) s = just c
  beval (le a₁ a₂) s = aeval a₁ s >>= λ v₁ -> aeval a₂ s >>= λ v₂ -> just (v₁ ≤ᵇ v₂)
  beval (not b) s = beval b s >>= λ b -> just (bnot b)
  beval (and b₁ b₂) s = beval b₁ s >>= λ b₁ -> beval b₂ s >>= λ b₂ -> just (b₁ ∧ b₂)
  ```,
  caption: "Agda interpreter for boolean expressions",
)<code-beval>

=== Commands <imp-semantics-commands>
The inference rules we give for commands follow the formalism of *big-step*
operational semantics, that is, intermediate states of evaluation aren't shown
explicitly in the rules themselves.

// @TODO - inference rules

In Agda, these rules are implemented as shown in @code-ceval.

#figure(
  ```hs
  mutual
   ceval-while : ∀ {i} (c : Command) (b : BExp) (s : Store) -> Thunk (Delay (Maybe Store)) i
   ceval-while c b s = λ where .force -> (ceval (while b c) s)

   ceval : ∀ {i} -> (c : Command) -> (s : Store) -> Delay (Maybe Store) i
   ceval skip s = now (just s)
   ceval (assign id a) s = now (aeval a s >>=m λ v -> just (update id v s))
   ceval (seq c c₁) s = ceval c s >>=p λ s' -> ceval c₁ s'
   ceval (ifelse b c c₁) s = now (beval b s) >>=p
    (λ bᵥ -> (if bᵥ then ceval c s else ceval c₁ s))
   ceval (while b c) s = now (beval b s) >>=p
    (λ bᵥ ->
     if bᵥ then (ceval c s >>=p  λ s -> later (ceval-while c b s))
     else now (just s))
  ```,
  caption: "Agda interpreter for commands",
  placement: auto
)<code-ceval>

=== Properties of the interpreter
Regarding the intepreter, the most important property we want to show puts in
relation the starting store a command is evaluated in and the (hypothetical)
resulting store. Up until now, we kept the mathematical layer and the code layer
separated; from now on we will collapse the two and allow ourselves to use
mathematical notation to express formal statements about the code: in practice,
this means that, for example, the mathematical names $"aeval"$,
$"beval"$ and $"ceval"$ refer to names from the code layer 
//typstfmt::off
```hs aeval```, ```hs beval``` and ```hs ceval```, respectively.
//typstfmt::on

#theorem(
  name: [`ceval` does not remove identifiers],
)[
    Let $c$ be a command and $sigma_1$ and $sigma_2$ be two stores. Then
    $ #conv($"ceval" c space sigma_1$, $sigma_2$) -> sigma_1 space subset.eq.sq^u sigma_2 $
    In Agda: 
//typstfmt::off
```hs 
ceval⇓=>⊑ᵘ : ∀ (c : Command) (s s' : Store) (h⇓ : (ceval c s) ⇓ s') -> s ⊑ᵘ s' 
``` 
//typstfmt::on
<ceval-store-inclusion>
]

#thmref(<ceval-store-inclusion>)[Theorem] will be fundamental for later proofs. 
