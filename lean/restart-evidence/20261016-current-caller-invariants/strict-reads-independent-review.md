# Independent review of current source-aligned read validity

Reviewed on 2026-10-16. No material defect was found in the seven frozen modules listed in the source hash manifest.

SourceCurrentAllocatedPrimaryReads.endpoint_closed explicitly indexes its trace with the same entry, edges, depth, free list, and heap as its literal SourceEndpointMemo.run call (lines 34-41). The full constructor signatures confirm that there is no separate trace entry or edge list. Its recursive predicate and unfolding constructors also retain the exact request. All 20 current constructors were inspected with explicit signature output.

PrimaryCompletion derives strict receipts from actual pure trace induction. completed_class extracts the pure trace from the actual bounded worker equation. complete_class independently derives the finite stable worker bound from the existing certified-node completion theorem. No final Valid premise occurs.

GateReadValidity follows supplied strict primary reads and supplied current secondary reads. Its unfolding helper identifies one literal unfold and its memo result by their actual execution equations. It derives intermediate heap readiness, availability, and table validity. It does not equate two different deep read schedules from equal returned heaps.

ReadDeterminism proves uniqueness only for fixed-fuel collection and exposure reads. The actual exposure validity proof aligns the supplied receipt with a correctness receipt at the same fuel, value, heap, and initial table. This is the bounded determinism fact needed by Required and Projection; it is not arbitrary deep receipt uniqueness.

SeededReadValidity follows head projection, actual tail, and actual checked native request. Its fold_effects helper constructs physical completion from initial invariants and reached ranges, then aligns the actual result and complete checked state using Fold.unique (lines 43-58). It retains the supplied actual read tables rather than substituting the constructed memo receipt. NativeReads.silent fixes the same bundle at both endpoints. The public range plan, original support, growth, and initial physical invariants remain explicit.

QueryReadValidity follows the supplied secondary gate, seeded fold, and current conjunction CallReads. It derives support from the actual false secondary trace. It constructs physical seeded completion from initial invariants and reached ranges and aligns the exact result and checked state with Seeded.unique. Its validity theorem consumes the supplied read receipts. No future Ready, final Valid, semantic parent law, or supplied successful child callback occurs.

PartialDescent uses the literal indexed Eq allocation with the actual returned operation state. All caller tables and native state remain unchanged. Its complete theorem derives operation growth, Ready, At, Sound, and inherited payload readiness. node_law has a clearly explicit child induction law; it only rewrites the actual child payload. It is not a general recursive caller completion theorem.

Validation: 28 public theorem axiom reports, 28 full theorem signatures, and 20 full constructor signatures pass with exit 0. Three independent integration kernels, their axiom reports, and full signatures pass with exit 0. They prove historical-versus-strict rejection, corrected execution on the same concrete resident trace, and primary-to-secondary-to-seeded-to-current-query composition with the literal returned tables and physical state. Only standard propext/Classical.choice/Quot.sound axioms occur. Final logs contain no warnings, errors, or sorryAx. The first kernel log records an invalid namespace alias and its cascading elaboration placeholders; it is retained. Only kernels-2.log is final evidence.

The separate supplied-read-index-review.md audits all 26 Required/Projection constructors and found no analogous drift. The historical primary counterexample is preserved in a new additive module. Haskell correspondence, lazy evaluation/publication, runtime identity, external solver behavior, and general recursive outer-caller completion are not established by this review.
