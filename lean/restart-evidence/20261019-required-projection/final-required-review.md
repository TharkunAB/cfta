# Independent Required and prepared projection review

Reviewed at 2026-10-19 00:54 CEST. No material issue was found in either
complete production proof. This review adds no Lean run or proof pair.

`SourceCurrentRequiredProjectionOrigins.lean` has SHA-256
`ebf430e8c217d2f6083ea23447ae56df5f4ede03a67341d407e002eca2abdc67`.
Its sole public theorem is `project_read`, at line 436.
`SourceCurrentRequiredTargetOperandOrigins.lean` has SHA-256
`ac1a8a8d1ff27a8a3a6705e370a1f5be738b248e82fb55c43e0ebe6357da42f0`.
Its sole public theorem is `operand`, at line 125.

The node theorem takes an explicit `Origin original prepared`. It takes a
false NodeTrace for the original value. It follows the actual Project of
the prepared value and the actual later Read of its returned result.
The conclusion retains an ordinary Route from the original value, full
RowOrigin fields, and ordered child Origins. It does not equate the rows.

The core `origin_plain` proof at line 102 preserves the hereditary Plain
annotation through all three Origin constructors and both ordered maps.
The `safe_origin` proof at line 137 uses the same signed child position on
both sides. `RowMap.indexed` supplies the actual original row. Its All₂
child relation supplies the child origin. No injective row map is assumed.
Normalization can remove or reorder rows.

The actual Project/ProjectRows induction at line 355 uses the lifted
acceptance predicate. Its union case at line 296 follows actual sequential
ReadAll states. It selects the full surviving physical row from the actual
constructor result. The acceptance invariant quantifies an actual Read,
not a structural RowAt. Thus an empty remaining path can return a Mu and
the later Read can unfold it. The Plain branch at line 273 excludes a
nonplain observed row using the exact reader's semantic, availability,
and causal guard facts. It does not rebase the observation to another heap.

The reader premises remain visible. The theorem requires SemanticReady
and causal Plain guard support at the reader, plus Keeps from the projection
return to that reader. Keeps supplies result availability. CostHeap is
required at the projection entry. It is not required at the final reader.
The guard support is a body/probe invariant on actual Mu records. It does
not require every source edge guard to be Plain.

The composite derives All₂ Origin and returned causal Guards from the
literal requireAll return, at lines 53 to 77. The original false class
derives the complete compiled exposure domain. The selected path alone
is not used to justify unrelated Required branches. Subsingleton equality
and letI only reconcile the fixed and generic DecidableEq instances.
They do not weaken the literal execution equations.

The composite keeps `values` and `prepared` distinct. Ordered All₂ recovers
both values at the same forest index. The false class is replayed on the
original values at requiredBefore. Historical UnionNormal is explicit at
that heap. There is no prepared false gate. The exact sameHeap premise
connects Required's return heap to the target operand's entry heap. It does
not permit an intervening native edit without another origin proof.

The target endpoint derives its actual projection and Merge stages at
their complete checked states. The observed positive result row yields an
indexed row in the projected value. Its nonempty own payload excludes a
Plain guard. The final Read used by the forest helper is at the exact
middle projection heap. The historical Merge Writer comes from explicit
Stored and Raw certificates. Raw includes the earlier actual writer; it
is not inferred from physical memo occupancy alone.

The conclusion retains the original ordinary Route, full original-to-
prepared row fields, and ordered Origin between original children and
prepared row children. The recursive Merge Run takes exactly those
prepared row children, in order. It may be the earlier warm writer's Run.
The identity alternative is explicit. Only original source children have
the strict mass bound. No mass bound on prepared or returned children is
claimed. No output child is equated with an original child.

The result is local to this actual Required and target operand phase.
Earlier class edits need their own source transport. The result does not
establish initial outer-input ancestry, full renewal, general completion,
or Haskell execution correspondence. It does not revive the false-primary
retention claim refuted by `required_changes_primary`.

The selected node receipts are required-projection-direct-2,
required-projection-canonical-1, and required-projection-public-1. The strict
source matches the production bytes and its log is literally empty.
The owner verifier was run read-only and returned PASS. The printer source
has SHA-256 `3a78bfc006d928d6087c9dcabf9d05c93835a1b2c2d691a0b28a1f2112310a38`.
Its complete 31,707-byte log has one full statement, proof, and axiom report.

The selected composite receipts are required-target-direct-5,
required-target-canonical-2, and required-target-public-1. Its strict log
is literally empty and its source matches the final production bytes.
The printer source has SHA-256
`e54f894908de535963c8ab5ff1d16ad184bce05c9aa627188a463f5ab67e76c6`.
Its complete 2,848,548-byte log has one full statement, proof, and axiom report.
Both printer groups use all eight required settings. Both contain only
propext, Classical.choice, and Quot.sound in the axiom report. Neither log
has a warning, error, printer failure, or omission marker. Both canonical
builds succeeded. Each replays only the unchanged ClosedCompletion:24:5
unused-input warning. No new warning is attributed to either module.

The final changed-child fixture has SHA-256
`c45ebc6cf0568471f8b6fbe5d3c70f6930d8dc26bf03ecbc0c93bf1e0f59c095`.
It builds a positive ordinary root with children `mu x. rec[x]` and a leaf.
The actual Required call changes the first child. All semantic, cost,
UnionNormal, guard, and availability facts come from the source build.
The initial Merge table is empty. The fixture invokes `operand`, then uses
Route[] and the actual Forest[0] to identify the unique source and prepared
rows. It proves ordered child Origin and unequal child lists. It supplies
no desired result or child-origin premise.

Its raw paths are `[[0],[0,0,0]]`. This is a valid Needed call test. It is
not a coherent normalized active equality class. The fixture does not prove
a false prepared gate. It does not assert finite-language productivity of
the used Mu. Its exported Merge child conclusion retains the identity-or-
ordered-Run alternative. It does not select the recursive arm. The final
projection root is ordinary. Mu exposure occurs inside Required. This is
not a forced final-Mu Read test or a warm Merge memo test.

The selected fixture strict receipt is required-target-kernels-direct-4.
Its source matches the final bytes and its log is literally empty.
The selected complete printer group is required-target-kernels-public-2,
with printer-source SHA-256
`e5005a6d52caedae4dc7302c61b29f10ccaa91315eb566c29c7c67751633e4d2`.
The final public theorem forwards a private checked witness. Exact text
comparison confirms that the old statement, private witness statement,
and final public statement are identical. The renamed private proof is
also identical to the old public proof. The first printer attempt ended
with -15 and remains unselected. Its cause is unknown. The final full
116,944-byte log uses all eight settings and only standard axioms. No
printer setting was weakened.

The review reuses two production public pairs, one constructed pair, and
three literal-empty strict logs. It owns zero Lean runs and zero new pairs.
No root helper, peaks file, mutable fixture, Audit, or authority document
is in this review's file footprint.
