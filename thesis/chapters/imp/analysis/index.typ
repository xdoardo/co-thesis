== Analyses and optimizations<section-analysis_optimization>
We chose to demonstrate the use of coinduction in the definition of operational
semantics implementing transformations on the code itself (that is, they are
static), then showing proofs regarding the result of the execution of the
program. The main inspiration for these operations is @concrete-semantics.

#include "./dia.typ"
#include "./fold.typ"
