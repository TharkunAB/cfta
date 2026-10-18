# Actual causal node source comparison

The public `node` theorem proves `CausalSourceRootLaw.Law (.node rows)` from that same law for each child of each original source row. The induction premise has this exact order:

```text
forall symbol guard children,
  EdgeSyntax.mk symbol guard children in rows ->
  forall child in children, Law child
```

The theorem retains the full existing source law. Both calls keep their actual initial contexts, assignments, names, cuts, and return states. Both returned heaps grow to one reader with the old payload contract and an empty-table history. No reader readiness, availability transport to the reader, issued extension, or returned-row survival premise is added.

The proof first splits the literal `buildEdges` schedules of both node calls. Their actual contexts and verified edge results supply the normality and residency needed by `StoredRootDeletionConstruction.makeNode`. The proof therefore reduces each result to the Boolean test that some actual row has assigned nonempty children. Root cuts do not enter ordinary nodes.

The row proof follows the two actual ordered source schedules. It preserves each original symbol, guard, and child order through `makeEdge_fields`. The tail starts at the actual edge constructor's return heap. Verified child, edge, and tail effects derive growth from each actual child return to the same reader. There is no warm replay or assumed intermediate growth.

For an original live row, the profile and live alias conditions restrict to each original child. The child law is instantiated with false cuts. The actual child return context and verified availability turn this uncut deletion result into assigned profile equivalence. Equivalent profiles have the same Empty test. Ordered child-list induction then gives equal assigned row-survival tests.

For an original dead row, no child comparison hypothesis or input-support agreement is needed. If all assigned child profiles were nonempty, no actual child could be literal Empty. The old actual source-profile theorem would then make the original symbolic row live, contradicting its dead status. This proves that a dead original row contributes false under every assignment on both sides. It does not require agreement on names used only in dead rows.

Finally, ordered row-list induction combines these equal Boolean tests. Both actual `makeNode` deletion formulas therefore return the same profile, which yields `Equivalent`. No output relation for the parent or its rows is assumed. The private live alias and physical source-liveness arguments reuse the proof pattern in the frozen `TrackedFilteredNodeFusion` module; that module was not changed.

Selected production SHA-256: `2d7dd361a4a4599bae78bd835797ff2db9a2922d4b2c52c1f9c663e366921498`. Strict attempt 1 returned 0 with a literal 0-byte log. Canonical build 1 returned 0 and completed 620 jobs without warnings. Public probe 1 returned 0 and printed the complete statement, proof, and axiom report with all eight required settings. Its log has 291597 bytes and uses only the standard allowed axioms. Each selected execution records effective 4 GiB maximum and high limits, zero swap, a five-minute cap, and Lean 4.34.1. There are no failed attempts or separate constructed pairs in this component.

The child law remains a strict source induction premise. This module does not independently prove the binder or union cases, an old payload-contract producer, general source comparison, general outer completion, or Haskell correspondence. The component manifest uses an explicit file list. No earlier source or evidence was changed.
