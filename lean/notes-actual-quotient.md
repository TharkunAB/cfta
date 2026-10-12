# Source actual classes and unambiguous guard correspondence

`ActualQuotient.lean` proves properties of the executed source representative
search. It covers all three cases: the equality callback, the equal named
leaf rule, and the original-path fallback. Every representative denotes the
same complete subtree as its actual. Complete representative search chooses
one canonical path for each complete subtree class.

`sparse_classes_refine_complete` proves that sparse allocation cannot combine
different complete actual classes. The proof uses the complete observation
adapter and the source callback code. It does not assume the desired
representative invariant. Equal inner actual terms at different positions
produce a source ambiguity witness. Complete comparison never produces such
a witness because it decides every pair of existing actual positions.

If the sparse ambiguity set is empty, `unambiguous_classes_exact` proves the
converse class relation. `unambiguous_representative_equal` then proves exact
equality of the chosen source paths. For leaves both callbacks agree. For
an inner term, absence of ambiguity forces the class to contain only that
position. `unambiguous_tables_equal` carries this equality through values,
conflicts, the finite fresh-name stream, allocations, and the per-path
declaration table. The sparse and complete tables are exactly equal.

`SourceGuardRefinement.lean` proves source evaluator correspondence for every
Guard constructor, including all list connectives and nested substitutions.
Its information order permits Unknown in the sparse result. A decided
sparse result must equal the complete result. `evaluate_refines` proves this
for fixed actual tables by induction over the actual executable evaluator.
`unambiguous_evaluator_refines` obtains table equality from the preceding
source allocation proof. `unambiguous_decided_exact` gives the final decided
result equality for public sparse and complete evaluator entry points.

These results hold for every stable scoped solver function and every formula
backend. They therefore apply to the concrete full-syntax backend from
SourceFormula without a solver-completeness premise. Solver soundness is
still necessary to interpret a solver verdict as a logical entailment.

The remaining case is a nonempty sparse ambiguity set with a decided guard.
That case can use a finer fresh-value partition than the complete evaluator.
SourceEntailment proves the required positive logical transport, but the
declaration table must still construct that transport for all nested scopes.
The pruner's refinement-only signature can also omit constructor names at
positions that do not require structural reads. Connecting that signature
to equivalent fresh-name choices remains separate from this same-term
sparse observation theorem.

Validation: `lake build MicroCFTA.SourceGuardRefinement` builds both modules
with the pinned toolchain. There are no proof placeholders or new axioms.
