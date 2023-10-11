== Analyses and optimizations<section-analysis_optimization>
We chose to demonstrate the use of coinduction in the definition of operational
semantics implementing transformations on the code itself, then showing proofs
regarding the result of the execution of the program. The main inspiration for
these transformations is @concrete-semantics, and they are _source to source_,
that is, they transform Imp programs to (pontentially untouched) Imp programs.

#include "./dia.typ"
#include "./fold.typ"
