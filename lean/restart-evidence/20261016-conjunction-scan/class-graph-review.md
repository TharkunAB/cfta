# Current conjunction Scan and range-plan review

Read-only review, 2026-10-16 06:57 CEST. No reviewed source was edited or
built. The Seeded dependency and final finite theorem were still being
written. This verdict covers the displayed graph, readiness helpers, and
range-plan definition. No material defect was found in that scope.

## Branch and state fidelity

`SourceCurrentConjunctionClassScan.Scan` (38–75) follows the source's
reached-class order. Primary false records a selected occurrence and runs
no secondary gate or query. Primary true and secondary true skip the
class without a query. Primary true and secondary false use the new
checked Seeded, followed by the CURRENT conjunction memo at the Seeded's
literal returned physical state. False memo answers resume the suffix at
`advancePhysical middle later` with the exact saved memo. True answers
stop without any suffix trace.

The equality-operation state is unchanged across gates. The new memo's
returned equality state is retained alongside its heap. The same native
node/edge tables and domain interner survive constructor-only advances.
No cold reset or unrelated final cache is introduced.

The graph's selected output on `some rejectedClass` is only the reached
selected prefix: preceding selected constructors prepend their classes to
the stopped constructor's empty list. That is consistent with the lazy
source partition and rejection guard, which does not consume the full
selected partition. `selected_sublist` claims only a sublist and preserves
occurrence order/multiplicity. The comments already say reached records.
Keep this distinction explicit in later public wrappers. Full selected
partition correspondence may be claimed only for a no-rejection result.

## Initial readiness and returned effects

`Ready` (110–115) records physical Good, SemanticReady, CostHeap, Scoped,
and Idle. It does not contain Contextual, NodeProduced, or a desired query
language law. This is suitable for physical finite Scan completion, not
by itself for common-language inclusion.

`advance_ready`, `primary_effects`, and `secondary_effects` derive the
returned invariants from actual physical effects and the current initial
readiness. The loaded-field annotation is transported through the real
gate constructor effects with the same equality state. Original forest
availability follows from the derived Keeps. No future ready/field
premise or universal conjoin-field closure is supplied.

The appended `memo_effects` uses the actual current Memo call to derive
that same returned readiness, Effects, final Correct, AnswerSound, and
Extends. Its initial memo correctness is explicit. Its result refers to
the actual `advancePhysical` state and saved memo.

The underlying `SourceCurrentAllocatedConjunctionMemo` adapter derives
physical readiness from Good/SemanticReady/CostHeap. Its `finite` calls
the new conjunction Memo completion, then derives its checked Receipt,
current Boolean memo correctness, AnswerSound, and retention. The warm
Boolean memo Correct premise is explicit and appropriate. It is not a
completed miss or desired answer premise. Contextual and scope transport
there act on unchanged native cells; they do not admit new model inputs.

## Range plan

`SourceCurrentConjunctionClassScanCompletion.Ranges` (26–47) recurses on
the strict original class suffix. Selected and skipped cases ask a suffix
range plan only at the actual returned gate state. Queried cases ask
SeededRanges at the actual primary/secondary anchor. A suffix plan is
required only after an actual Seeded and an actual FALSE new Memo call,
at its exact returned checked state and memo.

These completed graphs occur only as antecedents. The plan asserts no
existence of a query, final validity, availability, field closure,
semantic result, or memo correctness. It therefore does not hide a
future-success callback. There is no suffix plan for the true memo case.
The SeededRanges definition itself and the final finite proof require
their own review once frozen. This note does not validate an unwritten
finite theorem.

## Retained boundaries

The current graph composes the source schedule, checked native requests,
physical equality effects, and the fourth conservative Boolean memo.
Exact Seeded language inclusion, all three global gate/query memo call
receipts, host container/key correspondence, GHC forcing/publication,
and general constrained-caller termination remain separate. A final
physical Scan theorem must not be named or described as proving those
semantic or runtime transfers.

Reviewed SHA256 values at this intermediate source snapshot:

```
46edf035a9e6890053ccd6caee25052ca293e42277e10bbba75529f84fdd5cd1  SourceCurrentConjunctionClassScan.lean
a5f5be900c9775fce6a046b9b59447afab1ae69da2f972467cb4ec24d3684285  SourceCurrentConjunctionClassScanCompletion.lean
cba26b96b0bb99358f828dc62cb1175dff76af067acf46199670dfc9386c9c60  SourceCurrentAllocatedConjunctionMemo.lean
```
