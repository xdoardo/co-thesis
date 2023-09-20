#import "/includes.typ":*
#import "@preview/prooftrees:0.1.0"

=== Pure constant folding optimization<subsection-imp-analysis_optimization-fold>
Pure constant folding is the second and last operation we considered. Again from
@concrete-semantics, the operation of pure folding consists in statically
examining the source code of the program in order to move, when possible,
computations from runtime to (pre-)compilation.

The objective of pure constant folding is that of finding all the places in the
source code where the result of expressions is computable statically: examples
of this situation are `and true true`, `plus 1 1`, `le 0 1` and so on. This
optimization is called _pure_ because we avoid the passage of constant
propagation, that is, we don't replace the value of identifiers even when their
value is known at compile time.

==== Pure folding of arithmetic expressions<subsubsection-imp-fold-arith>
Pure folding optimization on arithmetic expressions is straighforward, and
we define it as a function ```hs apfold```. In words, what this optimization
does is the following: let $a$ be an arithmetic expression. Then, if $a$ is a
constant or an identifier the result of the optimization is $a$. If $a$ is the
sum of two other arithmetic expressions $a_1$ and $a_2$ ($a eq.triple "plus"
space a_1 space a_2$), the optimization is performed on the two immediate terms
$a_1$ and $a_2$, resulting in two potentially different expressions $a'_1$ and
$a'_2$. If both are constants $v_1$ and $v_2$ the result of the optimization is
the constant $v_1 + v_2$; otherwise, the result of the optimization consists in
the same arithmetic expression $"plus" space a_1 space a_2$ left untouched. The
Agda code for the function ```hs apfold``` is shown in @code-apfold.

#figure(```hs
apfold : (a : AExp) -> AExp
apfold (const x) = const x
apfold (var id) = var id
apfold (plus a₁ a₂) with (apfold a₁) | (apfold a₂)
... | const v₁ | const v₂ = const (v₁ + v₂)
... | a₁' | a₂' = plus a₁' a₂'
```, caption: "Agda code for pure folding of arithmetic expressions")<code-apfold>

Of course, what we want to show is that this optimization does not change the
result of the evaluation (#thmref(<thm-apfold-sound>)[Theorem]).
#theorem(
  name: "Soundness of pure folding for arithmetic expressions",
)[
    Let $a$ be an arithmetic expression and $s$ be a store. Then
    $ "aeval" a space s eq.triple "aeval" ("apfold" a) space s $

    In Agda: ```hs apfold-sound : ∀ a s -> (aeval a s ≡ aeval (apfold a) s) ```
    <thm-apfold-sound>
  ]
==== Pure folding of boolean expressions<subsubsection-imp-fold-bool>
//typstfmt::off
Pure folding of boolean expressions, which we define as a function ```hs bpfold```, 
//typstfmt::on
follows the same line of reasoning exposed in
@subsubsection-imp-fold-arith: let $b$ be a boolean expression. If $b$ is an
expression with no immediates (i.e. $b eq.triple "const" n$) we leave it
untouched. If, instead, $b$ has immediate subterms, we compute the pure folding
of them and build a result accordingly, as shown in @code-bpfold.

#figure(
```hs
bpfold : (b : BExp) -> BExp
bpfold (const b) = const b
bpfold (le a₁ a₂) with (apfold a₁) | (apfold a₂)
... | const n₁ | const n₂ = const (n₁ ≤ᵇ n₂ )
... | a₁ | a₂ = le a₁ a₂
bpfold (not b) with (bpfold b)
... | const n = const (lnot n)
... | b = not b
bpfold (and b₁ b₂) with (bpfold b₁) | (bpfold b₂)
... | const n₁ | const n₂ = const (n₁ ∧ n₂)
... | b₁ | b₂ = and b₁ b₂
```, 
caption: "Agda code for pure folding of arithmetic expressions"
)<code-bpfold>

As before, our objective is to show that evaluating a boolean expressions after
the optimization yields the same result as the evaluation without optimization.

#theorem(
  name: "Soundness of pure folding for boolean expressions",
)[
    Let $b$ be a boolean expression and $s$ be a store. Then
    $ "beval" b space s eq.triple "beval" ("bpfold" b) space s $

    //typstfmt::off
    In Agda: 
      ```hs 
      bpfold-sound : ∀ b s -> (beval b s ≡ beval (bpfold b) s) 
      ```
    //typstfmt::on
    <thm-bpfold-sound>
]

==== Pure folding of commands<subsubsection-imp-fold-commands>
Pure folding of commands builds on the definition of $"apfold"$ and $"bpfold"$
above combining the definitions as shown in @code-cpfold.

#figure(
```hs
cpfold : Command -> Command
cpfold skip = skip
cpfold (assign id a) 
  with (apfold a)
... | const n = assign id (const n) 
... | _ = assign id a 
cpfold (seq c₁ c₂) = seq (cpfold c₁) (cpfold c₂)
cpfold (ifelse b c₁ c₂) 
  with (bpfold b) 
... | const false = cpfold c₂ 
... | const true = cpfold c₁ 
... | _ = ifelse b (cpfold c₁) (cpfold c₂)
cpfold (while b c) = while (bpfold b) (cpfold c)
```,
caption: "Agda code for pure folding of commands"
)<code-cpfold>

And, again, what we want to show is that the pure folding optimization does not
change the semantics of the program, that is, optimized and unoptimized values
converge to the same value or both diverge
(#thmref(<thm-cpfold-sound>)[Theorem]).

#theorem(
  name: "Soundness of pure folding for commands",
)[
    Let $c$ be a command and $s$ be a store. Then
    $ "ceval" c space s eq.triple "ceval" ("cpfold" b) space s $

    //typstfmt::off
    In Agda: 
      ```hs 
        cpfold-sound : ∀ (c : Command) (s : Store) 
                        -> ∞ ⊢ (ceval c s) ≈ (ceval (cpfold c) s)
      ```
    //typstfmt::on
    <thm-cpfold-sound>
]

Of course, what makes #thmref(<thm-cpfold-sound>)[Theorem] different from the
other soundess proofs in this chapter is that we cannot use propositional
equality and we must instead use weak bisimilarity; we use the weak version as
in terms of chains of 
//typstfmt::off
```hs later``` and ```hs now```, if the optimization does indeed change the
syntactic tree of the command, if the evaluation converges to a value it may do
so in a different number of steps; for example, the program 
`while 1 < 0 do skip` will be optimized to `while false do skip`, 
resulting in a shorter evaluation, as `1 < 0` will not be evaluated at 
runtime.
//typstfmt::on
