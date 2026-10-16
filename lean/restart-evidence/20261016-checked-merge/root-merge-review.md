# Independent review of checked merge and projection

Read-only review. No source changes or builds. The reviewed frozen files are:

- `SourceCurrentAllocatedMerge.lean`: SHA256 `0b09416cda16796b7f14d62dae6954bcd9480dd120d4e92aa242bf289c7f9ec1`.
- `SourceCurrentAllocatedMergeOperand.lean`: SHA256 `40cb6d47de31a9d44c66dd6c09f9462b9a4a20ec3f19398ba0a15b68dffaa3b2`.
- `SourceCurrentConjunctionTargetProjection.lean`: SHA256 `577020368ab039941637724b2541221483390598542b14da355a3e1a92c2eccb`.

## Verdict

No material proof defect found. The adapters compose actual graphs and exact returned states. They do not derive a full Haskell execution theorem.

## Open siblings and projection domain

`TargetProjection.verified` (lines 65–98) uses `PathDomain.forest_effects` and `forest_heap` on the literal `Forest` receipt. `ForestClosed (index :: rest)` checks only the selected original value. `NodeClosed` checks only selected children at ordinary rows. Thus unrelated ordinary siblings may remain open. This is not a whole-forest closure premise.

`ForestClosed []` still requires all root values closed, and nonempty paths through Mu/union/reference heads retain the explicit whole-head closedness boundary. The new module does not infer this domain from an arbitrary false gate. `of_required` consumes the domain derived by the actual required receipt.

Proper-path language is inclusion of the accepted selected subtree, with its actual lookup premise. It is not exact projection language and does not retain ancestor guards. Root projection has exact union language. `MergeOperand` lines 86–91 compose these distinct facts correctly.

## Same graph and state

`Merge.verified` lines 107–121 first derives allocated physical effects from `call.verified`. Both global reads and independent language coverage then use the same `old := call.graph`, not a second merge or an uncached body replay. Erasure preserves the exact heap, result, and completed merge map; only equality allocation is erased.

Projection advances the same native state with the literal returned heap and unchanged operations (`TargetProjection.Receipt` lines 40–56). Merge advances it with its actual returned operation state. Native node/edge/domain tables remain equal. `At.advance` retains the fixed original interpretation and all existing cache admission facts. It does not admit a newly generated output into the old input inventory. Later query admission remains a separate operation, as the header states.

`MergeOperand.complete` lines 72–91 threads the exact projected value, middle checked state, and returned three-family global bundle into the merge. The stored merge memo grows through projection Keeps. The merge memo is not reset. Combined effects retain the original forest records without requiring those records closed.

## Selection predicate and warm semantic admission

The source comparison at `Interned/Operations.hs:672` requires literal `edgeConstraint wide == noConstraint`. `literalClear` models structural equality to the represented raw Top field. `normalized_clear_boundary` proves that `And []` can pass the older normalized plain predicate while failing this literal test. `source_finite` discharges the semantic clear callback with `literalClear_true`; it does not replace the actual selection receipt with a desired answer.

This is a pure represented-field predicate. The host Constraint/EqConstraints equality, interner identity, HashMap iteration/allocation, and runtime forcing correspondences remain outside this theorem. Completed selection receipts are source-model operations, not evidence that GHC forces every producer in this serial order.

The initial `∀ ambient, CacheCovers ... memo` premise in `Merge.verified`/`finite` is explicit semantic admission of the warm completed merge table. `Stored` and `At` alone do not imply it. It is independent of the new requested result and is preserved for every ambient by the same actual call. The empty cache can discharge this premise using the existing empty-cache theorem. A whole source runtime cache history is not established here.

## Retained limits

The result is merge language inclusion, not equality. It does not prove final generated-root admission, arbitrary cross-model warm cache validity, exact HashMap traversal, source publication before forcing, pending ancestor behavior, concurrency, machine identity capacity, or whole constrained-caller termination. No future final-state readiness, body completion, language law for the new parent, or completed projection is assumed by the finite endpoints.

## Artifact cleanup

Only the reviewer's derived `physical-deps/MicroCFTA/SourceCurrentAllocatedMergeGraph.olean` was removed. All human-readable isolated prefix sources and raw logs remain. The separate Graph.olean belongs to the graph worker; that worker was asked to remove its own compiled artifact.

The final directory scan found no `.olean`, `.ilean`, or `.o` files in this evidence directory.
