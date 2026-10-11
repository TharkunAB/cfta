# Signed guard and graph membership

`ConstraintIndicators` follows `Data.CFTA.Constraint.constraintIndicators`.
The model retains the coefficient-first source lists. It uses the actual
Cartesian conjunction, complement, left fold, and De Morgan disjunction.
`compile_correct` proves exact Boolean values for successful guard compilation.
`constraint_correct` includes normalized path equalities and contradictions.
`residual_error` preserves an unsupported guard as an error, even when the
equality part is false. No unsupported guard becomes an empty successful result.

Each atom is one path equality class. `SymbolicIndicators.classTest` gives
its exact subterm meaning. An empty class is true. Every path of a nonempty
class must exist and select the same term. This includes singleton and
repeated-path classes. The normalized equality representation still uses the
separate equality-completion correspondence.

`SignedUnion.union_indicator` proves the source union fold under numeric
multiplication for intersections. Only original alternatives need Boolean
values. This matters because the source edge datatype admits arbitrary
integer coefficients. A premise that every possible edge had a Boolean value
would exclude valid arithmetic intermediate representations.

`SymbolicIndicators.edgeValue_intersection` proves this numeric product law
for the actual symbolic edge intersection. It derives ordered child-domain
intersection, constructor matching, and signed guard multiplication.
`component_score` connects the literal raw component sum to this interpretation.
`expansion_indicators` then proves the complete nested source expression.

`counterMeaningFromRows` constructs the counter's semantic interface from
independent finite distinct languages, exact child intersection, successful
original guard compilation, and the graph's guarded row semantics. It assumes
no count result. `SymbolicCounter.counter_correct_mutual` uses this interface
to prove all six counter functions and their two memo tables.

The remaining graph boundary identifies source interned identities and graph
operations with these finite languages. The guard compiler proof covers the
supported structural fragment. Solver-dependent guards return residual errors
at this interface and use the separate refinement compilation path.
