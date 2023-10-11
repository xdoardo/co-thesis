#import "/includes.typ": *
== Related works<section-related>
The important aspect of this thesis is about the use of coinduction and sized
types to express properties about the semantics of a language. Of course, this
is not a new theoretical breakthrough, as it draws on a plethora of previous
works, such as @danielsson-operational-semantics and
@leroy-coinductive-bigstep.

The general objective is that of coming up with a representation of the
semantics of a language, be it functional or imperative, that allows a uniform
representation of both the diverging and the fallible behaviour of the
execution. Even if, surely, the idea comes up earlier in the literature, we choose
to cite @leroy-coinductive-bigstep, where the author uses coinduction to model
the diverging behaviour of the semantics of untyped λ-calculus but does so
using a relational definition and not an equational one, making proofs
concerning the semantics significantly more involved. 

With the innovations proposed by Capretta's `Delay` monad, a new attempt to
obtain such a representation was that of Danielsson in
@danielsson-operational-semantics; nonetheless, Agda's instrumentation for
coinduction was not mature enough: it used the so-called _musical notation_,
which suffered from the same limitations that regular induction has when using
a syntax-based termination or productivity checker, and it is also worth noting
that musical notation is potentially unsound when used together with sized
types @agda-docs. It would be unfair, however, not to mention that recent
updates to the code related to @danielsson-operational-semantics indeed uses
sized types and goes beyond using concepts from cubical type theory. 

In @concrete-semantics, the authors explore methods to apply transformations to
programs of an imperative language and prove the equivalence of the semantics
before and after such transformations; they do so using relational semantics
without the use of coinduction, thus not considering the "effect" of
non-termination. As noted, @concrete-semantics is the work we followed to come
up with transformations to explore.

In @nakata-coinductive-while, the authors show four semantics: big-step and
small-step relational semantics and big-step and small-step functional
semantics. They achieve so using Coq, which had no concept such as sizes.

In @hutton-compilers, the authors show how to implement correct-by-construction 
compilers targeting the Delay monad.

