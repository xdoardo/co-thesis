=== Pure constant folding optimization
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

// @TODO
