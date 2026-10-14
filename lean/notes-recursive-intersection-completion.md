# Actual nested native completion and retained enclosing cells

Proof checkpoint: `a674a61b`. Upstream: `f59c198d`, 2026-10-14.
Source: `Interned/Operations.hs:intersectOpen`, `intersectOpenEdge`, and
`Interned/FlatMemo.hs:lookupOrInsert`, `insert`, and `write`.

## Split actual native traces

`SourceRecursiveIntersectionNativeTraceSplit.steps_bind_inverse` splits an
actual completed appended trace into its completed inner body and outer
continuation. It derives the inner value, exact shared state, both finite
traces, and their original total step count. No body result or completion
provenance is supplied. Node and edge completion frame inversion derives
their exact one-step update and remaining continuation trace.

## Exact nested evaluation evidence

`SourceRecursiveIntersectionNativeEvaluation.Evaluation` records actual
physical effects, lookup and demand, completed compiled bodies, and their
original completion frames. Direct node calls, completed hits, and newly
started node and edge requests have separate rules. The judgment contains no
kernel execution, purity, language, or `Produced` premise.

`SourceRecursiveIntersectionNativeCompletion.evaluation_of_trace` uses strong
induction on the actual trace length to derive a finite nested evaluation.
`evaluation_of_done` obtains it from an actual completed bounded native run.
Each body segment is extracted from the original trace. The proof does not
assume that body completion occurred.

`SourceRecursiveIntersectionNativeEvaluationTrace.Evaluation.trace` constructs
the converse exact native trace. `Evaluation.done` supplies a sufficient bound
for that evaluation. `completed_iff_evaluation` proves agreement in both
directions, with the same returned value and complete source and memo state.
This is operational equivalence. It does not prove that every request has a
completed evaluation or a sufficient first-run bound.

## Source bodies and native completion frames

`SourceRecursiveIntersectionBodyCode.BodyCode` excludes explicit native
completion instructions. `compileNode_bodyCode` and `compileEdge_bodyCode`
derive this property for every compiled branch. Sequencing and ordered walks
retain it. Only the driver adds completion frames.

`FlatMemoThunkRunning` proves that fresh lookup and demand retain every
already-running cell. Completion preserves structural validity and changes
only its own cell. These laws do not assume anything about returned values.

`SourceRecursiveIntersectionNativeShape.Shape` retains fresh handles and
original node and edge request keys. It intentionally does not assert physical
input availability, word-key injectivity, or semantic completed provenance.
The stronger existing source `Valid` implies `Shape`. Lookup, demand, and
completion preserve this structural invariant. `Retains` records preservation
of every original running request in both families.

`SourceRecursiveIntersectionNativeRunning.Evaluation.retains` derives final
`Shape` and retention of all enclosing running cells from an actual completed
source-body evaluation and initial `Shape`. A nested completion cannot target
an already-running enclosing request: its own demand must have started a
different suspended cell. `done_retains` gives this result for actual completed
bounded runs. The proof covers all compiled node and edge bodies.

`node_body_cell` and `edge_body_cell` show that the original cell remains
running after its body completes. Its original completion frame then stores
the actual returned value in that exact captured request. This establishes
structural frame ownership. It does not establish `Produced` for that value.

## Next obligations

Completed native source execution now has full guarded kernel correspondence
and derived semantic memo provenance under the explicit checked word bounds.
`compileNode_safe` and `compileEdge_safe` derive physical continuation safety.
`Bounds.correct` derives final strong validity, exact physical/domain growth,
available results, stable kernel meaning, and `Produced` at new completion
frames. The node and edge API theorems start from actual native completion.
Read [native correctness](notes-recursive-intersection-native-correctness.md).

Derive physical input views, finite
reachable payload inventories, sufficient first-run bounds, and
`ProductReadback.members` and `.rejected`. `product_exact` gives product
language after those obligations. General open nested constructor completion,
new-body preparation, concrete GHC primitives and scheduling, and verified
Haskell extraction remain open. The exact Sized and cold-table results remain.

## Validation at this checkpoint

All eight new modules are imported by `MicroCFTA.Audit`. The pinned Lean 4.34.1
aggregate build passes 1,243 jobs and 41,062 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are used.
Log: `/tmp/mcfta-native-completion-20261014-audit.log`.
No Haskell source changed. Prior Nix and formatter checks remain the source
validation checkpoint. Prior proof, draft, and fixture bytes remain preserved
against the saved manifest.
