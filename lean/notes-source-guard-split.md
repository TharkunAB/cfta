# Semantic and structural guard splitting

`SourceGuardSplit` follows the current `Constraint.splitGuard` algorithm.
`containsSame` visits substitutions, negations, and both list connectives.
A guard without Same stays in the semantic component. An outer conjunction
splits each component with the source right fold. Each accumulator omits Top.
Every other guard containing Same stays intact in the structural component.

`semantic_clear` proves that the resulting semantic component contains no
Same, including inside nested scopes. `split_exact` proves that combining
the two component verdicts gives the original current public verdict.
It covers Yes, No, and Unknown, in either polarity. `split_yes` gives the
confirmed-language law used when pruning discharges only the semantic part.

The proof uses the repaired public Boolean dispatcher. Independent outer
operands allocate their own actual tables. Nonempty substitutions remain
opaque, so the proof does not distribute a conjunction through a substitution
scope or replace formula refutation with verdict negation.

Formula operations and solver calls remain pure parameters here. The theorem
does not equate IO call order, solver timeouts, or effects of a stateful callback.
The earlier `Guards.splitGuard_preserves` result uses a smaller binary syntax;
this module supplies the complete current source syntax and entry behavior.
