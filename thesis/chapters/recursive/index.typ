= Recursive datatypes and proofs<chapter-recursive>

All throughout this work we make use of the mathematical technique called
_coinduction_. It is far from easy to come up with  an intuitive and contained
explaination for this technique, as coinduction is a pervasive topic in
computer science and mathematics and can be explained with different flavours
and intuitions: in category theory as coalgebras, in automata theory and formal
languages as a tool to compare infinite languages and automata execution, in
real analysis as greatest fixed points, in computer science as infinite
datatypes and corecursion and much more.

We examine this last possibility, as our use of coinduction is "limited" to
coinductive datatypes and proofs by corecursion. We begin introducing induction
both as a mathematical tool and in computer science, in particular in Agda. We
then move to coinduction and its mathematical intepretation; we conclude this
chapter with an explaination of how recursive definitions are handled in proof
assistants such as Agda.

#include "co-induction.typ"
#include "agda.typ"
