#import "@preview/prooftrees:0.1.0"
#import "/includes.typ": *

== Semantics <imp-semantics>
Having understood the syntax of Imp, we can move to the _meaning_ of Imp
programs. We will explore the operational semantics of the language using the
formalism of inference rules, then we will show the implementation of the
semantics (as an intepreter) for these rules.

Before describing the rules of the semantics, we will give a brief explaination
of what we expect to be the result of the evaluation of an Imp program. 

#code(label: <code-imp-simple>)[`if true then skip else skip`]

An example of Imp program is shown in @code-imp-simple. In general, we can
expect the evaluation of an Imp program to terminate in some kind value or
diverge. But what happens when, as mentioned in
@subsection-imp-introduction-syntax[Subsection], an unitialized identifier is
used, as shown for example in @code-imp-failing? The execution of the program
cannot possibly continue, and we define such a state as _failing_ or _stuck_
(see also @section-convergence[Section]).

Of course, there is a plethora of other kinds of failures we could model, both
deriving from static analysis or from the dynamic execution of the program (for
example, in a language with divisions, a division by 0), but we chose to model
this kind of behaviour only.

#code(label: <code-imp-failing>)[`while true do x <- y`]

We can now introduce the formal notation we will use to describe the semantics
of Imp programs. We already introduced the concept of store, which keeps track
of the mutation of identifiers and their value during the execution of the
program. We write #conv([c, $sigma$], $sigma_1$) to mean that the program $c$,
when evaluated starting from the context $sigma$, converges to the store
$sigma_1$; we write #fails([c, $sigma$]) to say that the program $c$, when
evaluated in context $sigma$, does not converge to a result but, instead,
execution gets stuck (that is, an unknown identifier is used).

The last possibility is for the execution to diverge, #div([c, $sigma$]): this
means that the evaluation of the program never stops and while no state of
failure is reached no result is ever produced. An example of this behaviour is
seen when evaluating @code-imp-diverging.

#code(label: <code-imp-diverging>)[`while true do skip`]

We are now able to give inference rules for each construct of the Imp language:
we will start from simple ones, that is arithmetic and boolean expressions, and
we will then move to commands. The inference rules we give follow the formalism
of *big-step* operational semantics, that is, intermediate states of evaluation
are not shown explicitly in the rules themselves.

=== Arithmetic expressions <imp-semantics-arithmetic_expressions>
Arithmetic expressions in Imp can be of three kinds: integer ($ZZ$) constants,
identifiers and sums. As anticipated, the evaluation of arithmetic expressions
can fail, that is, the evaluation of arithmetic expressions is not a total
function; again, the possibile erroneous states we can get into when evaluating
an arithmetic expression mainly concerns the use of undeclared identifiers.

Without introducing them, we will use notations similar to that used earlier for
commands, in particular #conv($dot.c$, $dot.c$). 
#figure(
  grid(
    columns: (1fr, 1fr, 1fr),
    rows: (40pt),
    prooftrees.tree(prooftrees.axi[], prooftrees.uni[#conv([const n, $sigma$], [n])]),
    prooftrees.tree(
      prooftrees.axi[$id in sigma$],
      prooftrees.uni[#conv([var id, $sigma$], [$sigma id$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 4pt, [#conv([$a_1$ , $sigma$], [$n_1$])])),
      prooftrees.axi(pad(bottom: 4pt, [#conv([$a_2$, $sigma$], [$n_2$])])),
      prooftrees.nary(2)[#conv([$"plus" a_1 a_2$, $sigma$], [$(n_1 + n_2)$])],
    ),
  ),
  caption: "Inference rules for the semantics of arithmetic expressions of Imp",
  supplement: "Table",
)<imp-arith-semantics>

The Agda code implementing the interpreter for arithmetic expressions is shown
in @code-aeval. As anticipated, the inference rules denote a partial
function; however, since the predicate $id in sigma$ is decidable, we can make
the interpreter target the `Maybe` monad and make the intepreter a total
function.

#mycode(label: <code-aeval>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Semantics/BigStep/Functional/Arith.agda#L16")[
//typstfmt::off
```hs
aeval : ∀ (a : AExp) (s : Store) -> Maybe ℤ
aeval (const x) s = just x
aeval (var x) s = s x
aeval (plus a a₁) s = aeval a s >>= λ v₁ -> aeval a₁ s >>= λ v₂ -> just (v₁ + v₂)
```
//typstfmt::on
]

=== Boolean expressions <imp-semantics-boolean_expressions>
Boolean expressions in Imp can be of four kinds: boolean constants, negation of
a boolean expression, logical conjunction and, finally, comparison of arithmetic
expressions.

#figure(
  grid(
    columns: (1fr, 1fr),
    rows: (40pt, 40pt),
    prooftrees.tree(prooftrees.axi[], prooftrees.uni[#conv([const c, $sigma$], [c])]),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#conv([b, $sigma$], [c])])),
      prooftrees.uni[#conv([$not b$, $sigma$], [$not c$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 4pt, [#conv([$a_1$, $sigma$], [$n_1$])])),
      prooftrees.axi(pad(bottom: 4pt, [#conv([$a_2$, $sigma$], [$n_2$])])),
      prooftrees.nary(2)[#conv([le $a_1$ $a_2$, $sigma$], [$(n_1 < n_2)$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 4pt, [#conv([$b_1$, $sigma$], [$c_1$])])),
      prooftrees.axi(pad(bottom: 4pt, [#conv([$b_2$, $sigma$], [$c_2$])])),
      prooftrees.nary(2)[#conv([and $b_1$ $b_2$, $sigma$], [$(c_1 and c_2)$])],
    )
  ),
  caption: "Inference rules for the semantics of boolean expressions of Imp",
  supplement: "Table",
)<imp-bool-semantics>

The line of reasoning for the concrete implementation in Agda is the same as
that for arithmetic expressions: the inference rules denote a partial function;
since what makes this function partial -- the definition of identifiers -- is a
decidable property, we can make the interpreter for boolean expressions a total function
using the `Maybe` monad, as shown in @code-beval.

#mycode(label: <code-beval>,"https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Semantics/BigStep/Functional/Bool.agda#L20")[
//typstfmt::off
```hs
beval : ∀ (b : BExp) (s : Store) -> Maybe Bool
beval (const c) s = just c
beval (le a₁ a₂) s = aeval a₁ s >>= 
  λ v₁ -> aeval a₂ s >>= 
    λ v₂ -> just (v₁ ≤ᵇ v₂)
beval (not b) s = beval b s >>= λ b -> just (bnot b)
beval (and b₁ b₂) s = beval b₁ s >>= 
  λ b₁ -> beval b₂ s >>= 
    λ b₂ -> just (b₁ ∧ b₂)
```
//typstfmt::on
]

=== Commands <imp-semantics-commands>
#figure(
  tablex(
    columns: (140pt, auto, 160pt, 60pt),
    auto-vlines: false,
    auto-hlines: false,
    
    prooftrees.tree(prooftrees.axi[], prooftrees.uni[#conv([skip , $sigma$], [$sigma$])]),
    [$arrow.b.double$skip],
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#conv([a , $sigma$], [v])])),
      prooftrees.uni[#conv([$"assign" id a$, $sigma$], [$"update" id v space sigma$])],
    ),
    [$arrow.b.double$assign],
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [#conv([$c_1$, $sigma$], [$sigma_1$])])),
      prooftrees.axi(pad(bottom: 5pt, [#conv([$c_2$, $sigma_1$], [$sigma_2$])])),
      prooftrees.nary(2)[#conv([$"seq" space c_1 space c_2$, $sigma$], [$sigma_2$])],
    ),
    [$arrow.b.double$seq],
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [#conv([$c^t$, $sigma$], [$sigma^t$])])),
      prooftrees.axi(pad(bottom: 5pt, [#conv([$b$, $sigma$], [$"true"$])])),
      prooftrees.nary(2)[#pad(top: 5pt, conv([$"if" b "then" c^t "else" c^f$, $sigma$], [$sigma^t$]))],
    ),
    [$arrow.b.double$if-true],
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [#conv([$c^f$, $sigma$], [$sigma^f$])])),
      prooftrees.axi(pad(bottom: 5pt, [#conv([$b$, $sigma$], [$"false"$])])),
      prooftrees.nary(2)[#pad(top: 5pt, conv([$"if" b "then" c^t "else" c^f$, $sigma$], [$sigma^f$]))],
    ),
    [$arrow.b.double$if-false],
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [#conv([$b$, $sigma$], [$"false"$])])),
      prooftrees.uni[#pad(top: 5pt, conv([$"while" b "do" c$, $sigma$], [$sigma$]))],
    ),
    [$arrow.b.double$while-false],
    colspanx(4, align: center,
    grid(columns: 2,
     column-gutter: 10pt,
     prooftrees.tree(
        prooftrees.axi(pad(bottom: 5pt, [#conv([$b$, $sigma$], [$"true"$])])),
        prooftrees.axi(pad(bottom: 5pt, [#conv([$c$, $sigma$], [$sigma'$])])),
        prooftrees.cobin[#conv([$"while" b "do" c$, $sigma$], [$sigma'$])],
      ), [#v(50%)$arrow.b.double$while-true#v(50%)])), 
  ),
  caption: "Inference rules for the semantics of commands",
  supplement: "Table",
)<imp-commands-semantics>

We need to be careful when examining the inference rules in
@imp-commands-semantics. Although they are graphically rendered the same, the
convergency propositions used in the inference rules are different from those
in @imp-semantics-boolean_expressions or @imp-semantics-arithmetic_expressions.
In fact, while in the latter the only modeled effect is a decidable one, the
convergency proposition here models two effects, partiality and failure. While
failure, intended as we did before, is a decidable property, partiality is not,
and we cannot design an interpreter for these rules targeting the `Maybe` monad
only: we must thus combine the effects and target the `FailingDelay` monad, as
shown in @section-convergence[Section]. The code for the intepreter is shown in
@code-ceval.


#mycode(label: <code-ceval>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Semantics/BigStep/Functional/Command.agda#L23")[
//typstfmt::off
```hs
mutual
 ceval-while : ∀ {i} (c : Command) (b : BExp) (s : Store)  
                -> Thunk (Delay (Maybe Store)) i
 ceval-while c b s = λ where .force -> (ceval (while b c) s)

 ceval : ∀ {i} -> (c : Command) -> (s : Store) -> Delay (Maybe Store) i
 ceval skip s = now (just s)
 ceval (assign id a) s =
    now (aeval a s) >>= λ v -> now (just (update id v s))
 ceval (seq c c₁) s =
    ceval c s >>= λ s' -> ceval c₁ s'
 ceval (ifelse b c c₁) s =
    now (beval b s) >>= (λ bᵥ -> (if bᵥ then ceval c s else ceval c₁ s))
 ceval (while b c) s =
    now (beval b s) >>=
      (λ bᵥ -> if bᵥ
        then (ceval c s >>=  λ s -> later (ceval-while c b s))
        else now (just s))
```
//typstfmt::on
]

The last rule (`while` for `beval b` converging to `just true`) is coinductive,
and this is reflected in the code by having the computation happen inside a
`Thunk` (see @subsubsection-sizes-coinduction[Section])

=== Properties of the interpreter
Regarding the intepreter, the most important property we want to show puts in
relation the starting store a command is evaluated in and the (hypothetical)
resulting store. Up until now, we kept the mathematical layer and the code layer
separated; from now on we will collapse the two and allow ourselves to use
mathematical notation to express formal statements about the code: in practice,
this means that, for example, the mathematical names $"aeval"$,
$"beval"$ and $"ceval"$ refer to names from the "code layer"
//typstfmt::off
```hs aeval```, ```hs beval``` and ```hs ceval```, respectively.
//typstfmt::on

#lemma(label: <lemma-ceval-store-tilde>)[
Let $c$ be a command and $sigma_1$ and $sigma_2$ be two stores. Then

#align(
  center,
  $#conv($"ceval" c , sigma_1$, $sigma_2$) -> sigma_1 space ∻ sigma_2$,
)

#mycode(proof: <proof-ceval-store-tilde>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Semantics/BigStep/Functional/Properties.agda#L90")[
//typstfmt::off
```hs
ceval⇓=>∻ : ∀ (c : Command) (s s' : Store) (h⇓ : (ceval c s) ⇓ s') -> s ∻ s'
```
//typstfmt::on
]]

@lemma-ceval-store-tilde[Lemma] will be fundamental for later proofs. 

It is also important, now that all is set up, to underline that the meaning of
#conv([c, $sigma$], $sigma_1$), #fails([c, $sigma$]) and #div([c, $sigma$])
which we used giving an intuitive description but without a concrete
definition, are exactly the types described in @section-convergence[Section],
with the parametric types adapted to the situation at hand: thus, saying
#conv([c, $sigma$], $sigma_1$) actually means that $"ceval" space "c" space
sigma ≋ "now" ("just" sigma_1)$, #div([c, $sigma$]) means that $"ceval" space
"c" space sigma ≋ "never"$ and #fails([c, $sigma$]) means that $"ceval"
space "c" space sigma ≋ "now" "nothing"$. 
