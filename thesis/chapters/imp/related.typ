#import "/includes.typ": *
#pagebreak()

== Related works<section-related>
The important aspect of this thesis is about the use of coinduction and sized
types to express properties about the semantics of a language. Of course, this
is not a new theoretical breakthrough, as it draws on a plethora of previous
works, such as @danielsson-operational-semantics and @leroy-coinductive-bigstep.

Our work implements an _imperative_ language using _sized_ types to target the
_coinductive_ `FailingDelay` monad. Many of the works in literature -- for
example @danielsson-operational-semantics, @leroy-coinductive-bigstep, and
@abel-miniagda -- chose to implement lambda calculus and its typed variants.
Furthermore, some of the cited articles target the `Delay` or `FailingDelay`
monad, but not each of them uses sized types; for example,
@danielsson-operational-semantics does not use sizes, albeit a newer version of
the code in the paper does. 


#todo[To cite: Danielsson's operational semantics - Leroy's coinductive big step operational semantics - Abel (various) - Hutton's Calculating dependently-typed compilers (functional pearl) ]
