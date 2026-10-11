# Recursive probe metadata

`RecursionProbe.lean` implements the minimum-size convergence loop in
`Gen.Internal.Recur.recur`. The initial body is built with no known finite
member. The next assumption retains the least discovered finite size.
Every later recursive call uses a strictly smaller natural size.

`convergeFinite_correct` derives the exact returned body, stable assumption,
and a bound on body constructions. `converge_correct` proves stability for
any total body builder. If the initial body reports minimum `n`,
`converge_steps` bounds the total number of body constructions by `n + 2`.
This is termination of the control loop. It does not prove that an arbitrary
Haskell callback terminates when the loop invokes it.

`dispatch` models the public precedence: opaque bodies remain opaque,
construction failures retain their errors, bodies without the occurrence
remain finite, live unguarded recursion fails, and live empty recursion fails.
`recursive_dispatch` derives the exact conditions on successful recursive
metadata. No successful empty language is substituted for an unknown failure.

`MinimumExpr` implements the source's minimum rules for occurrences, finite
sources, pay, atomic boundaries, choices, and products. `evaluate_monotone`
derives monotonicity from these operations. `converge_fixed` proves that a
monotone builder stops at an actual fixed minimum, not only a stable running
minimum. `expression_minimum_fixed` applies this result without assuming the
fixed-point postcondition for a standard source expression.

`WeightExpr` follows the disjunction of weighted flags through choices and
products. `weighted_probe_fixed` and `weighted_probe_least` prove that the
source's one probe with a false recursive flag computes the least stable
weighted flag for this algebra. Thus an intrinsic atomic weight is not hidden
by an unweighted recursive placeholder.

Source correspondence still requires the Haskell builder to use these
metadata operations consistently. Arbitrary inspection-dependent builders,
`StableName` token allocation, lazy knot productivity, and finite discovery
of grouped-family keys are separate obligations. The model does not claim
that an arbitrary Haskell function is parametric or terminates.

Validation: `lake build MicroCFTA.RecursionProbe` succeeds with the pinned
toolchain. The file uses no `sorry` or additional axioms.
