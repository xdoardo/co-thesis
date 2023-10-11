#import "@local/summary:1.0.0": *

#import "./includes.typ": *
#set cite(style: "numerical")
#show bibliography: set text(13pt)

#show: summary.with(
  title: "Program Transformations in the Delay Monad",
  subtitle: "A Case Study for Coinduction via Copatterns and Sized Types",
  author: "Edoardo Marangoni",
  figure: align(bottom, image("./figures/Minerva.png", width: 28%)),
  university: [University of Milan],
  department: [Department of Computer Science and Technology],
  degree: "Master of Science",
  msg: include "./msg.typ",
  supervisor: [Prof. Alberto Momigliano],
  year: [Academic Year 2022-2023], 
  number: [num. 973597], 
)

= Summary
Our objective is to define an _operational semantics_ for an _imperative
language_ targeting an adequate _monad_ to model the desired _effects_, all in
a _dependently typed_ _proof assistant_. This work, in a nutshell, is a case
study to analyse how all these techniques work when put together.

_Program transformations_ are the final end of our work. A program transformation is
an operation that changes in some way an input program in some source language
in another program in a target language. Examples of program transformations
are the static analysis of the source code such as _constant folding_, _dead
code elimination_, _register allocation_, _liveness analysis_ and many more
@allen-catalogue. The kind of transformations just cited are _source to
source_, that is, the transformation is a function from the input language and
outputs a program in the same language.

Another important program transformation are _compilers_ for which, in general,
we often take the correctness for granted: in this case the transformation
outputs, generally, a result in a different language, for example assembly code
for an input in the C language.

Having a formal statement that proves that the transformations operated on a
program do not change the semantics of the source language is obviously a much
desired feature, and many efforts in the literature have been in this
direction. One of the most notable ones is CompCert @compcert, which has the
objective of providing a formalized backend for (almost all of) the ISO C
standard by providing a compiler where the majority of transformations (all, if
we do not consider lexical analysis and printing to ASM as transformations) are
either programmed in Caml or programmed and proved in Coq @coq. 

Our work draws inspiration from seminal works like @leroy-coinductive-bigstep
and @danielsson-operational-semantics: both use _coinduction_ to define the
semantics of the language, but do not make use of the same techniques we
explore, namely sized types (which are not present in
@danielsson-operational-semantics) and the use of the `Delay` monad proposed by
Capretta @capretta-delay, which does not appear in @leroy-coinductive-bigstep. These two
techniques together allow the definition of a functional interpreter which is
then used throughout the work. 

The objective, then, is to implement program transformations: we chose two
transformations as formally described by Nipkow in @concrete-semantics; once
implemented, we show that the transformation either helps proving a theorem on
the execution of the program (namely, that if the analysis validates the
program its execution will not fail) or it is then proved that it does not
change the result of the execution.



#pagebreak()
#bibliography("./db.bib")
