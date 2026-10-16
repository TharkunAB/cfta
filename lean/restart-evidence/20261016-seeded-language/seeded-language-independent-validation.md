# Independent checked seeded-language validation

Date: 2026-10-16 08:01 CEST.

Source SHA256: `9bdf2f2d893aaf6667e71f5cc062162b3622bfae62397924a818ae199dddd598`.

The root reported the canonical build GREEN1227. This independent check ran direct Lean against the completed canonical dependencies. It passed with exit status 0 and no warnings, errors, or `sorryAx`.

Command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-seeded-language/seeded-language-independent-probes.lean
```

Five public theorem endpoints have axiom reports and complete signatures:

- `fold_complete`
- `seeded_complete`
- `Seeded.receipt`
- `false_class_complete`
- `false_class_receipt`

`Includes` and `Receipt` also have full signature checks. Five named integration kernels have their own axiom reports and complete signatures. Totals: 10 axiom reports and 12 signatures. Every axiom set is a subset of `propext`, `Classical.choice`, and `Quot.sound`.

## Integration kernels

`empty_seed` derives the empty endpoint through `seeded_complete`. Actual-graph uniqueness identifies both the literal empty result and the exact unchanged checked state. The resulting inventory retains At. The empty endpoint does not claim unconditional common-part inclusion.

`two_path_order` completes paths `[first, second]`. Inversion of the actual result exposes projection of `second`, then projection of `first`, then the actual checked request on those two returned values. It retains the precise intermediate states, actual physical trace, final receipt, and common-part inclusion.

`three_path_order` completes paths `[first, second, third]`. Inversion exposes projections in the order `second`, `third`, `first`. The first actual native trace intersects the third value with the first-seed value. The outer actual trace intersects the second value with that tail result. Both reached checked states and trace indices are retained. The final receipt and common-part inclusion refer to that same output.

`actual_trace_receipt` supplies an actual Seeded graph and uses the receipt endpoint. It derives At, Good, output closedness and availability, same-cache physical Fields, and the nonempty common-part inclusion law. It supplies no result law or future final-state invariant. The endpoint aligns the completed construction with the supplied graph by value and complete checked-state uniqueness.

`seeded_then_generated` completes an arbitrary nonempty seeded fold and feeds its actual output into the next generated native query. It uses that result as both operands of the next intersection. The final seeded receipt supplies Good, At, Scoped, SemanticReady, Idle, availability, and closedness. The only added premise after that receipt is the next reached WordRanges. The query wrapper derives the actual next Inventory and final At. Its literal checked done, closed resident output, and common selected-part inclusion follow from its exact intersection receipt. This is a concrete continuation integration; it does not claim every possible next operand has the common-part property.

## Scope and checks

The source proof follows head projection, recursive tail, and final native request, after the first-seed rotation. The two- and three-path kernels check this order from the actual graph. Selected proper path support is explicit. The original sibling forest need not be wholly closed. Initial Good, physical Ready, Scoped, Idle, inventory At, forest availability, anchor support, and actual-prefix reached-range plans remain explicit.

The language conclusion is common-part inclusion. It is not a claimed exact characterization of all seeded output terms. The proof does not equate this checked conjunction graph with the historical eager graph. GHC scheduling, solver IO, and runtime correspondence remain separate.

The first raw probe log retains one missing evidence-only section variable in the empty kernel. The final probe instantiates the irrelevant empty-case unconstrained predicate explicitly. All named kernels have explicit final axiom reports, so automatic recovery placeholders cannot pass the evidence check unnoticed.

No proof source was edited. No canonical Lake build ran. Only new evidence files with the `seeded-language-independent-` prefix were written. The guard agent reviews the source semantics separately.
