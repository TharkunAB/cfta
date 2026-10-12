# Current equality guards and symbolic indicators

`SourceEqualityGuards` connects the existing signed indicator compiler to
the repaired public guard evaluator. Its `BooleanGuard` is exactly the
supported Top, Bottom, Same, Not, And, and Or syntax. `source` retains the
current source constructors, list order, and repeated operands. Theory and
substitution guards remain residual compiler errors outside this fragment.

`same_exact` derives the complete Same verdict from actual path lookups and
structural term equality. Both paths must exist. A reflexive pair does not
turn a missing path into a successful equality. Empty substitution stacks
leave the full annotated trees unchanged.

`evaluate_exact` proves agreement with Boolean evaluation in either source
polarity. Supported complete guards cannot produce Unknown and require no
solver stability or completeness premise. `compiled_exact` then connects
the actual signed coefficient algorithm to the current confirmed language.

The source emits each equality pair as a two-path class. `pair_class` proves
that this class has precisely the current Same meaning. `classes_score`
preserves the complete signed sum when pairs become classes.
`constraint_exact` combines those rows with stored normalized equality
classes. `constraint_rows` derives successful compilation and the exact
edge-score law for every complete term. This supplies the Boolean-guard
premise used by the symbolic count/select/rank proofs.

Paths use the existing natural-index model. Host signed path conversion,
physical containers, and the Haskell-to-Lean transcription remain separate
interfaces. This result does not add symbolic support for solver-dependent
or substitution guards. It states their existing unsupported boundary.
