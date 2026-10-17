# Initial instruction profile

The frozen source has SHA256 `0298f96dbe864237b2c2e200166a1c85c77e2ce317ed9777fda3e45472399422`.
It defines one fixed source branching limit and a pure rank recurrence.
The limit is `max 1 (max (rows * rows) (max members arity))`.
The counts come from successful reads in the initial issued payload ranges.
They cover Mu, reference, union, and ordinary operands.
There is no restriction on guards, symbol values, or identifier magnitudes.

The literal symbol join retains duplicate occurrences.
Its length is bounded by the product of the two original row counts.
The two union bounds use the actual member lists.
The child bound uses the exact ordered zip.
`NodeScope` and `EdgeScope` retain the original heap operands.
These lemmas do not bound generated output profiles.

The recurrence has `budget L 0 = 0` and `budget L (h + 1) = 4 + L * budget L h`.
The source limit is at least one.
The arithmetic lemmas permit every natural `L`, including zero.
They prove monotonicity in `L` and `h` and a lower bound of four at positive rank.
No theorem connects this credit to completed instruction execution in this module.
The compiler and execution proofs must supply that connection.
No completed receipt, desired result law, or future width certificate occurs in the public hypotheses.

The final strict source check exited zero with an empty log.
The canonical build completed 1175 jobs and replayed one existing ClosedCompletion linter warning.
All 20 public declaration pairs and two integration pairs passed strict imported checks.
Their signatures include explicit arguments, universes, and proof terms.
Their axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.

The first integration constructs a return for arbitrary closed source syntax.
It derives Facts, Original, and initial NodeScope before it applies the new bounds.
The second integration constructs a source union with a recursive Mu member and an ordinary member.
Its actual source limits are rows 6, members 2, and arity 5.
Its branching limit is 36.
It has two literal union members, two equal-symbol row pairs, and a selected row with two zipped children.
The integration derives EdgeScope from the actual original node and its resident row.
It computes rank-three credit as 5332.
It does not assume source completion or a completed query as an input.

The failed initial shell path and first kernel draft remain in separate logs.
The first kernel draft had an EdgeKey field-order error and a simplifier target error.
The final production source did not change after its strict successful check.
