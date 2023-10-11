#import "/includes.typ":*
#import "@preview/prooftrees:0.1.0"

=== Pure constant folding optimization<subsection-imp-analysis_optimization-fold>
Pure constant folding is the second and last transformation we consider.
Again from @concrete-semantics, pure folding consists in statically examining
the source code of the program in order to move, when possible, computations
from runtime to (pre-)compilation. 

The objective of pure constant folding is that of finding all the places in the
source code where the result of expressions is computable statically: examples
of this situation are `and true true`, `plus 1 1`, `le 0 1` and so on. This
optimization is called _pure_ because we avoid the phase of constant
propagation, that is, we do not replace the value of identifiers even when their
value is known at compile time.

==== Pure folding of arithmetic expressions<subsubsection-imp-fold-arith>
Pure folding optimization on arithmetic expressions is straighforward, and we
define it as a function ```hs apfold```. In words : let $a$ be an arithmetic
expression. Then, if $a$ is a constant or an identifier the result of the
optimization is $a$. If $a$ is the sum of two other arithmetic expressions
$a_1$ and $a_2$ ($a eq.triple "plus" space a_1 space a_2$), the optimization is
performed on the two immediate terms $a_1$ and $a_2$, resulting in two
potentially different expressions $a'_1$ and $a'_2$. If both are constants
$v_1$ and $v_2$ the result of the optimization is the constant $v_1 + v_2$;
otherwise, the result of the optimization consists in the same arithmetic
expression $"plus" space a'_1 space a'_2$, that is, optimized immediate
subterms. The Agda code for the function ```hs apfold``` is shown in
@code-apfold.

#mycode(label: <code-apfold>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/PureFolding/Arith.agda#L15")[
//typstfmt::off
```hs
apfold : (a : AExp) -> AExp
apfold (const x) = const x
apfold (var id) = var id
apfold (plus a₁ a₂) with (apfold a₁) | (apfold a₂)
... | const v₁ | const v₂ = const (v₁ + v₂)
... | a₁' | a₂' = plus a₁' a₂'
```
//typstfmt::on
]

Of course, what we want to show is that this optimization does not change the
result of the evaluation, as shown in @thm-apfold-safe[Theorem].
#theorem(
  name: "Safety of pure folding for arithmetic expressions",
  label: <thm-apfold-safe>
)[
    Let $a$ be an arithmetic expression and $s$ be a store. Then

    #align(center, 
    $"aeval" a space s eq.triple "aeval" ("apfold" a) space s$)

    In Agda: 
#mycode(proof: <proof-apfold-safe>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/PureFolding/Arith.agda#L31")[
  ```hs apfold-safe : ∀ a s -> (aeval a s ≡ aeval (apfold a) s) ```
]] 

#linebreak()
==== Pure folding of boolean expressions<subsubsection-imp-fold-bool>
//typstfmt::off
Pure folding of boolean expressions, which we define as a function ```hs bpfold```,
//typstfmt::on
follows the same line of reasoning shown in
@subsubsection-imp-fold-arith[Paragraph]. 
Let $b$ be a boolean expression. If $b$ is an expression with no immediates
(i.e. $b eq.triple "const" n$) we leave it untouched. If, instead, $b$ has
immediate subterms, we compute the pure folding of them and build a result
accordingly, as shown in @code-bpfold.

#mycode(label: <code-bpfold>,"https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/PureFolding/Bool.agda#L17")[
//typstfmt::off
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
... | b₁' | b₂' = and b₁' b₂'
```
//typstfmt::on
]

As before, our objective is to show that evaluating a boolean expression after
the optimization yields the same result as the evaluation without optimization, 
as shown in @thm-bpfold-safe.

#theorem(
  name: "Safety of pure folding for boolean expressions",
  label:  <thm-bpfold-safe>
)[
    Let $b$ be a boolean expression and $s$ be a store. Then
    #align(center, $"beval" b space s eq.triple "beval" ("bpfold" b) space s$)

#mycode(proof: <proof-bpfold-safe>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/PureFolding/Bool.agda#L38")[
    //typstfmt::off
      ```hs
      bpfold-safe : ∀ b s -> (beval b s ≡ beval (bpfold b) s)
      ```
    //typstfmt::on
  ]]
==== Pure folding of commands<subsubsection-imp-fold-commands>
Pure folding of commands builds on the definition of $"apfold"$ and $"bpfold"$
above combining the definitions as shown in @code-cpfold.
#mycode(label: <code-cpfold>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/PureFolding/Command.agda#L23")[

//typstfmt::off
```hs
cpfold : Command -> Command
cpfold skip = skip
cpfold (assign id a) with (apfold a)
... | const n = assign id (const n) 
... | _ = assign id a 
cpfold (seq c₁ c₂) = seq (cpfold c₁) (cpfold c₂)
cpfold (ifelse b c₁ c₂) with (bpfold b) 
... | const false = cpfold c₂ 
... | const true = cpfold c₁ 
... | _ = ifelse b (cpfold c₁) (cpfold c₂)
cpfold (while b c) with (bpfold b)
... | const false = skip
... | b = while b c
```
//typstfmt::on
]

And, again, what we want to show is that the pure folding optimization does not
change the semantics of the program, that is, optimized and unoptimized programs
converge to the same value or both diverge, as shown in @thm-cpfold-safe[Theorem].

#theorem(
  name: "Safety of pure folding for commands",
  label: <thm-cpfold-safe>
)[
    Let $c$ be a command and $s$ be a store. Then
    #align(center, $"ceval" c space s eq.triple "ceval" ("cpfold" b) space s$)

  #mycode(proof: <proof-cpfold-safe>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Analysis/PureFolding/Command.agda#L50")[
    //typstfmt::off
      ```hs
        cpfold-safe : ∀ (c : Command) (s : Store)
                        -> ∞ ⊢ (ceval c s) ≈ (ceval (cpfold c) s)
      ```
    //typstfmt::on
]] 

Of course, what makes @thm-cpfold-safe[Theorem] different from the other safety
proofs in this chapter is that we cannot use propositional equality and we must
instead use weak bisimilarity. The execution of a program, in terms of chains
of constructors ```hs later``` and ```hs now```, changes for the same term if 
the pure folding optimization does indeed change the source. Take, for example, 
the case for `c ≡ while (plus 1 1) < 0 do skip`; this program will be optimized to 
`skip`, which results in a shorter evaluation.
