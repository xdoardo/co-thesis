#import "@preview/prooftrees:0.1.0"
#import "/includes.typ": *

== Semantics <imp-semantics>
Having understood the syntax of Imp, we can move to the _meaning_ of Imp
programs. We'll explore the operational semantics of the language using the
formalism of inference rules, then we'll show the implementation of the
semantics (as an intepreter) for these rules.

Before describing the rules of the semantics, we will give a brief explaination
of what we expect to be the result of the evaluation of an Imp program. As shown
in @imp-syntax-rules, Imp programs are composed of three entities: arithmetic
expression, boolean expression and commands.

#code(ref: <code-imp-simple>)[`if true then skip else skip`]

An example of Imp program is shown in #coderef(<code-imp-simple>). In general,
we can expect the evaluation of an Imp program to terminate in some kind value
or diverge. But what happens when, as mentioned in
@subsection-imp-introduction-syntax[Subsection], an unitialized identifier is
used, as shown for example in #coderef(<code-imp-failing>)? The execution of
the program cannot possibly continue, and we define such a state as _failing_ or
_stuck_ (see also @section-convergence[Section]).

Of course, there is a plethora of other kinds of failures we could model, both
deriving from static analysis (such as failures of type-checking) or from the
dynamic execution of the program, but we chose to model this kind of behaviour
only.

#code(ref: <code-imp-failing>)[`while true do x <- y`]

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
seen when evaluating #coderef(<code-imp-diverging>)

#code(ref: <code-imp-diverging>)[`while true do skip`]

We're now able to give inference rules for each construct of the Imp language:
we'll start from simple ones, that is arithmetic and boolean expressions, and
we'll then move to commands.

=== Arithmetic expressions <imp-semantics-arithmetic_expressions>
Arithmetic expressions in Imp can be of three kinds: integer ($ZZ$) constants,
identifiers and sums. As anticipated, the evaluation of arithmetic expressions
can fail, that is, the evaluation of arithmetic expression is not a total
function; again, the possibile erroneous states we can get into when evaluating
an arithmetic expression mainly concerns the use of undeclared identifiers.

Without introducing them, we will use notations similar to that used earlier for
commands (#conv($dot.c$, $dot.c$) and #fails($dot.c$))
#figure(
  grid(
    columns: (1fr, 1fr, 1fr),
    rows: (40pt),
    prooftrees.tree(prooftrees.axi[], prooftrees.uni[#conv([const n], [n])]),
    prooftrees.tree(
      prooftrees.axi[$id in sigma$],
      prooftrees.uni[#conv([var id], [$sigma id$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#conv([$a_1$], [$n_1$])])),
      prooftrees.axi(pad(bottom: 2pt, [#conv([$a_2$], [$n_2$])])),
      prooftrees.nary(2)[#conv([$"plus" a_1 a_2$], [$(n_1 + n_2)$])],
    ),
  ),
  caption: "Inference rules for the semantics of arithmetic expressions of Imp",
  supplement: "Table",
)<imp-arith-semantics>


The Agda code implementing the interpreter for arithmetic expressions is shown
in #coderef(<code-aeval>). As anticipated, the inference rules denote a partial
function; however, since the predicate $id in sigma$ is decidable, we can make
the interpreter target the `Maybe` monad and make the intepreter a total
function.

#mycode(ref: <code-aeval>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Semantics/BigStep/Functional/Arith.agda#L16")[
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
    prooftrees.tree(prooftrees.axi[], prooftrees.uni[#conv([const c], [c])]),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#conv([b], [c])])),
      prooftrees.uni[#conv([$not b$], [$not c$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#conv([$a_1$], [$n_1$])])),
      prooftrees.axi(pad(bottom: 2pt, [#conv([$a_2$], [$n_2$])])),
      prooftrees.nary(2)[#conv([le $a_1$ $a_2$], [$(n_1 < n_2)$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#conv([$b_1$], [$c_1$])])),
      prooftrees.axi(pad(bottom: 2pt, [#conv([$b_2$], [$c_2$])])),
      prooftrees.nary(2)[#conv([and $b_1$ $b_2$], [$(c_1 and c_2)$])],
    )
  ),
  caption: "Inference rules for the semantics of boolean expressions of Imp",
  supplement: "Table",
)<imp-bool-semantics>

The line of reasoning for the concrete implementation in Agda is the same as
that for arithmetic expressions: the inference rules denote a partial function;
since what makes this function partial -- the definition of identifiers -- is a
decidable property, we can make the interpreter for boolean expressions a total function 
using the `Maybe` monad, as shown in #coderef(<code-beval>).

#mycode(ref: <code-beval>,"https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Semantics/BigStep/Functional/Bool.agda#L20")[
//typstfmt::off
```hs
beval : ∀ (b : BExp) (s : Store) -> Maybe Bool
beval (const c) s = just c
beval (le a₁ a₂) s = aeval a₁ s >>= λ v₁ -> aeval a₂ s >>= λ v₂ -> just (v₁ ≤ᵇ v₂)
beval (not b) s = beval b s >>= λ b -> just (bnot b)
beval (and b₁ b₂) s = beval b₁ s >>= λ b₁ -> beval b₂ s >>= λ b₂ -> just (b₁ ∧ b₂)
```
//typstfmt::on
]

=== Commands <imp-semantics-commands>
The inference rules we give for commands follow the formalism of *big-step*
operational semantics, that is, intermediate states of evaluation are not shown
explicitly in the rules themselves.

#figure(
  tablex(
    columns: 3,
    auto-vlines: false, 
    auto-hlines: false,
    prooftrees.tree(prooftrees.axi[], prooftrees.uni[#conv([skip , $sigma$], [$sigma$])]),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 2pt, [#conv("a", "v")])),
      prooftrees.uni[#conv([$"assign" id a$, $sigma$], [$"update" id v space sigma$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [#conv([$c_1$, $sigma$], [$sigma_1$])])),
      prooftrees.axi(pad(bottom: 5pt, [#conv([$c_2$, $sigma_1$], [$sigma_2$])])),
      prooftrees.nary(2)[#conv([$"seq" space c_1 space c_2$, $sigma$], [$sigma_2$])],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [#conv([$c^t$, $sigma$], [$sigma^t$])])),
      prooftrees.axi(pad(bottom: 5pt, [#conv([$b$, $sigma$], [$"true"$])])),
      prooftrees.nary(2)[#pad(top: 5pt, conv([$"if" b "then" c^t "else" c^f$, $sigma$], [$sigma^t$]))],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [#conv([$c^f$, $sigma$], [$sigma^f$])])),
      prooftrees.axi(pad(bottom: 5pt, [#conv([$b$, $sigma$], [$"false"$])])),
      prooftrees.nary(2)[#pad(top: 5pt, conv([$"if" b "then" c^t "else" c^f$, $sigma$], [$sigma^f$]))],
    ),
    prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [#conv([$b$, $sigma$], [$"false"$])])),
      prooftrees.uni[#pad(top: 5pt, conv([$"while" b "do" c$, $sigma$], [$sigma$]))],
    ), 
    colspanx(3)[
    #prooftrees.tree(
      prooftrees.axi(pad(bottom: 5pt, [#conv([$b$, $sigma$], [$"true"$])])),
      prooftrees.axi(pad(bottom: 5pt, [#conv([$c$, $sigma$], [$sigma'$])])),
      prooftrees.cobin[#conv([$"while" b "do" c$, $sigma$], [$sigma'$])],
    )
    ]
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
only, we must thus combine the effects and target the `FailingDelay` monad, as
shown in @section-convergence[Section]. The code for the intepreter is shown in
#coderef(<code-ceval>).


#mycode(ref: <code-ceval>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Semantics/BigStep/Functional/Command.agda#L23")[
//typstfmt::off
```hs
mutual
 ceval-while : ∀ {i} (c : Command) (b : BExp) (s : Store) -> Thunk (Delay (Maybe Store)) i
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

The last rule (`while` for `beval b` convering to `just true`) is coinductive,
and this is reflected in the code by having the computation happen inside a
`Thunk`, that is, the actual tree of execution is expanded only when the
computation is forced.

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

#lemma()[
Let $c$ be a command and $sigma_1$ and $sigma_2$ be two stores. Then

#align(center,
$#conv($"ceval" c , sigma_1$, $sigma_2$) -> sigma_1 space ∻ sigma_2$)

#mycode(proof: <proof-ceval-store-tilde>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Semantics/BigStep/Functional/Properties.agda#L90")[
//typstfmt::off
```hs
ceval⇓=>∻ : ∀ (c : Command) (s s' : Store) (h⇓ : (ceval c s) ⇓ s') -> s ∻ s'
```]
//typstfmt::on
<lemma-ceval-store-tilde>
]

#thmref(<lemma-ceval-store-tilde>)[Lemma] will be fundamental for later proofs.
