#import "/includes.typ": *

#pagebreak(to: "odd")
#pagebreak(to: "odd")
= Conclusions<chapter-conclusions>

We defined an operational semantics for Imp targeting the `Delay` monad which,
together with the `Maybe` monad, provided an adequate type to model the effects
of divergence and failure: we did this with the aid of Agda, and we explored
the implementation of such a semantics using sized types.

Our objective, other than the definition itself, was to use the semantics
defined this way to show how it can be used when transforming a source program.
The transformations we chose to implement, both suggested by Nipkow in
@concrete-semantics, explore two source to source transformations. 

The first, _definite initialization analysis_ is, as the name suggests, a
static check and in fact leaves the source code untouched; it provides,
however, useful insights on the behaviour of the program when executed: if no
`dia` relation can be built for the program at hand, it means that the program
will surely crash and fail. On the other hand, if there exists a construction
for `dia` for the program at hand, we are assured that the program will not
fail -- of course, it can still diverge.

The second, _pure folding optimization_, is a transformation that has the
objective to lift information that is statically known to avoid run-time
computations. We proved that this transformation, which indeed changes the
syntactic structure of the program, does not change its semantics.

All throughout the work, _sizes_ proved to be useful in the definitions and to keep
track of termination and productivity: if compared with early versions of
@danielsson-operational-semantics, one important difference is that, for
example, we did not have to "trick" the termination checker, but every
definition was fairly streamlined. We can also compare our realization with the
work of Leroy in @leroy-coinductive-bigstep and @leroy-mechsem, which uses a
relational definition of the semantics of Imp, which can make proofs more
involved.

== Future works
We chose to model only one kind of failure: an extension using `Result := Ok v | Error e` 
and a monad based on that type is fairly straightforward. The list of possible
optimizations is long and well described in the literature: an interesting work
can be the implementation of a general-purpose back-end and investigate various
optimiziations used in the industry, starting from the translation of a
low-level intermediate representation into static single-assignment form or
continuation-passing style, proving easy properties of the transformations.
