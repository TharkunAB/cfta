# Lattice variable-order retries

The source is `Data.CFTA.Refinement.Lattice.points` and `latticeEntailment`.
`LatticeRetry.namedLevels` removes coordinates from the last index to zero.
It records the declared name on a failed elimination. `namedLevels_erases`
proves that removal of this diagnostic gives `LatticeLevels.buildLevels`
exactly. `namedPoints_erases` extends this result through parsing, retained
levels, and the integral count check. Every failed elimination names a
declared variable.

`attempt` follows the source retry policy. Only `NonUnitCoefficient` can
start a retry. The failed name moves to the first position, unless it is
already there. Each move decreases a natural-number budget. The initial
budget is the number of declared names. The loop does not try every
permutation. A remaining unsupported case returns Unknown.

`moveFirst_perm` proves that each move preserves the distinct variable list.
`attempt_origin` proves that every result, including an error, comes from an
actual query in a permutation of that list. `attempt_ne_nonintegral` excludes
the internal count assertion failure. `attempt_zero_iff` proves that a zero
count means no named integer valuation satisfies the formula.

`attempt_api_exact` composes the successful retry with the actual polynomial
decoder. The stored count is exact. Each valid integer tuple has one rank.
The decoder is injective. Tuple coordinates use the final variable order.
`implication_yes` and `implication_no` prove the definite entailment verdicts
over all named integer valuations. The No verdict supplies a counterexample.

The proof takes the duplicate-free name list produced by the source adapter.
Concrete `nubOrd`, `Text` conversion, binding freshening in scoped entailment,
machine indexes, and map storage remain representation obligations. The
proof does not assert that retries make every integer formula countable.

Validation: `lake build MicroCFTA.LatticeRetry` succeeds with the pinned
toolchain. There are no proof placeholders or additional axioms.
