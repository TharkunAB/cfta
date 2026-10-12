# Full source indicator compiler adapter

`MicroCFTA.SourceIndicatorCompiler` models the full `Guard` dispatch in
`Data.CFTA.Constraint.constraintIndicators`. It imports the equality semantics
and signed-series proofs from `SourceEqualityGuards` and `ConstraintIndicators`.
It does not assume that a compiled row has the correct score.

`guardTerms` and `guardList` implement the source constructor cases and the
left-to-right `traverse`. Each `Same left right` emits one raw class
`[left, right]`. The Cartesian products, complements, list order, duplicate
rows, and integer coefficients remain explicit. The conversion lemmas prove
that these exact rows equal the class representation of the generic compiler.

`successful_fragment` extracts a supported Boolean guard and its exact generic
compilation from any successful full-source result. `source_compile` proves
the converse with exact output rows. `successful_iff_supported` states the
complete supported-syntax boundary. The corresponding constraint theorems
include the stored normalized equality classes and their exact row product.

Unsupported `Entails`, `Satisfies`, `Holds`, and `Substitute` return the complete
encountered guard. The compiler does not inspect a substitution body. This
includes `Substitute []`, even though the public evaluator treats that empty
wrapper as an identity. `first_error` and `boolean_first_error` prove that a
successful list prefix preserves the first failure and ignores the suffix.
Negation preserves the error payload. Stored equalities do not suppress an
error. Kernel-checked examples cover false conjunctions, true disjunctions,
contradictory stored equalities, negation, and opaque empty substitutions.

`successful_guard_score` connects any successful full-source guard compilation
to the current public complete-term evaluator. `successful_constraint_score`
adds the normalized equality component. Its conclusion has the score form
required by the `compiled` premise in `SymbolicInternedView.allocated_total_api`.
Thus this premise follows from actual successful compiler output for the
supported source syntax. Graph allocation and graph-row association remain
separate premises of that API.

The model uses the existing `SourceGuards.Path` representation and normalized
equality adapter. This module does not prove Haskell extraction, path conversion,
equality normalization, theory solver correctness, or graph construction. It
proves the pure compiler over the full source guard syntax. No source repair is
required for this adapter.

Validation: `lake -d lean build MicroCFTA.SourceIndicatorCompiler` with the
pinned Lean 4.34.1 toolchain. No external axioms, `sorry`, or `native_decide` are
used.
