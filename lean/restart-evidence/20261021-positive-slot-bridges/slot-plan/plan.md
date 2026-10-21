# Positive positions for completed class target slots

Date: 2026-10-21 05:48 CEST.
Status: source-only proposal. No implementation or Lean check is in this package.
This package has zero Lean jobs and zero new proof pairs.

## Exact fixed-capture slot law

Use the values captured by ONE actual class.
They remain fixed while that class forces multiple targets.
They need not equal the prepared Required forest or another class's phase values.
For each slot action `a` and full target `t`, the needed law is:

```lean
before.targets a = some t →
∀ q : List Nat, PositiveAt t q →
∃ index path original,
  ((index :: path).map Int.ofNat) ∈ operandPaths record.paths a ∧
  values[index]? = some original ∧
  PositiveAt original (path ++ q)
```

This is the precise forest interpretation of a competing path followed by the SAME positive suffix q.
The natural competing path is `index :: path`.
Its first index selects the captured forest value.
Its remaining path is appended to q inside that value.
Do not append the forest index to a Node PositiveAt path.
Do not convert arbitrary negative signed paths to natural indices.
`operandPaths` comes from natural class paths and its membership supplies the exact natural witness.

The proposed sole public `RawCorridorSharedTargetPositivePositions.force_receipt` takes the SAME supplied completed Force receipt.
It takes the entry slot law above for existing slots.
It returns that law for every actual final slot.
It also retains the existing final cap Stored, current-source native positive Support, actual causal publication history and Merge positive Support.
The complete argument/result sketch is in `proposed-contract.lean.txt`.
No new public predicate or historical receipt type is needed for this first bounded result.

The initial slot law is immediate for `SharedTargetState.initial`, whose targets are all None.
A warm hit needs the entry law for the exact present value in the exact slot.
Ready's historical SlotReceipt alone does not imply the new positive law.
It retains a past completed graph, but does not supply positive native and Merge entry laws at that past call.
Current positive support cannot be transported backward to that historical writer.
The new invariant must be established before storage and retained by literal hits and unchanged-slot advances.

## Small projection consequence

Use the separately assigned additive `RawCorridorPositiveValue.project` consequence of the existing public raw observers:

```lean
(project : Project (p.map Int.ofNat) input before result after)
(semantic : SemanticReady before) (costs : CostHeap before)
(available : Available before input) (guards : GuardHeap Plain before)
(corridor : RawCorridor (p.map Int.ofNat) input)
(positive : PositiveAt result q) :
PositiveAt input (p ++ q)
```

Here p is the projection path. q is the independent positive suffix.
If p is empty, Project.root is identity, including when input is a literal union.
Return the supplied PositiveAt proof directly.
An empty q does NOT make a nonempty projection identity.
For a nonempty p and empty q, use the raw root observer.

For nonempty p, derive Ordinary result from the actual Project and its physical effects.
Project.empty returns Empty.
Project.ordinary ends in a literal source Union, which reads rows and makes an ordinary node.
Project.recursive follows its actual Head effects and the same nonempty remaining Project.
The existing private `project_ordinary` in TargetOperandPositivePosition is a short reusable proof pattern for that separate producer.
The slot consumer must use the new public result consequence once it is checked.
It must not copy the projection induction again.
No recursive exposure or projection proof of hundreds of lines must be copied.

PositiveAt on an ordinary result has only a root-row or ordered-child case.
The literal `.node` result admits a zero-fuel `Read.done 0 rfl` at the actual Project return heap.
Its rows are exactly that full node's rows.
Use actual project effects for return SemanticReady and reflexive Keeps.
Use ProjectionGuard.node for the return GuardHeap.
Apply RawCorridorPositiveProjection.root for a root positive.
Apply its child theorem for an ordered child positive.
Empty has no PositiveAt proof; a union-positive constructor contradicts Ordinary result.
The zero-fuel ordinary Read is derived locally and does not assume a future read or callback completion.

For Forest `(index :: p).map Int.ofNat`, a missing root produces Empty and has no positive.
A selected root supplies the SAME signed lookup.
Convert that lookup to `values[index]?` and use the new public Project consequence.
No whole-root cap is required; only the selected raw corridor is used.

## Actual operand

Unpack the SAME `AllocatedMergeOperand.Receipt.actual` once.
Keep its projected value, middle state, projection receipt and allocated Merge receipt together.
Use RawCorridorProjectionCap.forest to obtain a finite cap for that actual projected value.
Use MergePositivePosition.call on the SAME `merged.actual` call.graph.
Its positive law relates the actual returned first winner to the full projected input.
Its physical Stored premise and actual projected availability justify full-input warm readback.
It is not a law for an independently chosen candidate.
Compose its result-to-projection law with the small private Forest wrapper above.

Use ConstrainedCapMemoMerge.retained on that SAME actual call.graph to obtain its output cap and final conditional Merge law.
Use actual projection guard preservation, CurrentNative.advance and ConstrainedCapMergeJointEffects.merge for Current at the returned states.
No cap is transported backward.
No all-root cap or false gate is assumed for the captured phase forest.

The operand introduces no native node or edge cells.
Its receipt supplies literal nodes and edges equalities.
For its positive native store, use the separately assigned additive `NativePositiveSupportAdvance.advance` once it is checked.
Its exact arguments are currentBefore, Support beforeHeap before.native, Good after, actual Kernel.Extension and literal node/edge table equalities.
Its proof builds `Support sourceBefore after.native` from those unchanged tables.
It builds `Origins.Stored sourceBefore after.native` from currentBefore.2.2 and those SAME equalities.
Existing NativePositiveSupportRebase.rebase then uses source facts, actual return facts, forward growth and issued extension.
The result rebases the SAME captured requests and cells.
Do not use bare Grows to infer their input laws.
This specific bridge adds no general state or history framework.
Positive Support alone needs no after-semantic, guard or causal-history premise in this bridge.
Current and causal-history preservation remain separate obligations.

ParentPublicationHistory.operand, line 33, already derives the actual whole operand publication interval.
Compose it with the supplied initial causal history to obtain the returned causal history.
It uses RequiredPublicationHistory.forest and MergePublicationHistory.merge internally.
Do not infer a causal interval from growth or unchanged native cells.

## Fold and target

Use a new joint induction on the SAME actual FoldReads.
The nil case is exactly its operand receipt.
The cons case follows the actual order: head operand, recursive tail, then native query.
Retain the fixed class capture and every operand's exact natural member of seed :: paths.

The head operand returns its cap, positive law, current native support and both Merge laws.
The recursive tail starts at that exact returned state and table.
It receives the forward captured availability and the SAME returned causal history.
Its result includes the actual tail cap and same-path positive-source law.

At the actual native query, choose max headDepth tailDepth.
Grow the head's availability through the literal tail effects.
Use the head and tail closedness from their actual receipts.
Apply NativeCurrentPositivePositions.step ONCE to query.actual at the tail's return.
Its positive conclusion is exactly:

```lean
PositiveAt queryResult q → PositiveAt headResult q ∨ PositiveAt tailResult q
```

Compose the chosen side with that side's actual operand-path source law.
The suffix q is unchanged in both branches.
The same step supplies final Current, native positive Support, causal history and result cap.
The native query changes no Merge table.
Physical Merge Stored moves through its actual effects.

Target.nil returns Empty and cannot have a positive occurrence.
Target.nonempty uses this same Fold induction.
No alternative operand schedule or generated query completion is assumed.

## Force store and hit

For a hit, receipt.reads identifies exactly the present entry and the unchanged state.
Use the supplied entry slot law for that SAME action and full value.
The existing cap Stored supplies the same-value cap.
Current, native positive Support, causal history and both Merge laws remain unchanged.

For a miss, the SAME TargetReads yields the target result law and all returned stores.
Store that law at the actual action.
For another action, retain the exact old target lookup and its entry law.
The real absent premise rules out a previous value at the stored action.
There is no fresh target writer selection or copied slot from a different capture.
The force result's ancestry also follows from final-slot law and receipt.present.

## Existing cap endpoint and real remaining access boundary

RawCorridorSharedTargetCap.force_receipt, line 142, is public and supplies final cap Stored and a finite cap of the forced value.
It can be called ONCE on the same supplied Force receipt to retain those existing final cap fields.
It does not export caps of each internal head and tail before native combination.
Its operand_cap, fold_cap and target_cap, lines 62, 93 and 125, are private.
The new joint induction therefore still needs small local operand-cap plumbing through public RawCorridorProjectionCap.forest and Merge.retained.
The output cap from NativeCurrentPositivePositions.step then feeds later combinations.
This is the genuine local proof work; a wrapper around the final cap theorem alone cannot prove the new Force law.

Do not clone the 169-line module wholesale or modify its frozen source.
Reuse its public final Force endpoint and the public projection, Merge, advance, publication and native-step endpoints.
Use the two separately checked small bridges, actual operand composition and joint Fold/Target induction.
An expected slot implementation is about 260–350 lines with one public Force theorem, excluding those separate bridge modules.
If its full expanded invariant statements or shape proof exceed about 450 lines, request a scope review before adding a public framework.
This is an estimate, not checked proof evidence.

At this plan's initial draft, RawCorridorPositiveValue.project and NativePositiveSupportAdvance.advance were unproved assigned dependencies.
Their authors report successful strict checks for frozen sources b55beb19 and d0b9482f.
Root now reports both official source installations and independent literal-empty strict checks.
This package pins those official source statements and retains the identical earlier author snapshots.
It adds no Lean check of them.
Their FULL readbacks and root canonical approval remain separate owner/root evidence.
The slot theorem must wait for the official dependency import cue before its first proof check.
The slot producer itself remains unimplemented and unproved.

## Relation to Required and chronological class captures

RequiredCorridorChronology.pass supplies raw corridor preservation, final Current and conditional Merge-cap laws.
The earlier selected-mask producer and all₂_signed derive the masks for the literal tail-produced phaseValues.
Keep those phaseValues fixed inside their class.
Do not replace them with the original prepared forest.
Do not replay a false Required gate on phaseValues.

TargetLaterHeapPositivePosition.operand supplies original-index ancestry only when its capture is the literal Required prepared forest.
It cannot be applied directly to a changed class capture just because that capture is available later.
The new raw-mask endpoint intentionally returns ancestry in the actual SAME class capture instead.

The chronological corridor theorem does not yet supply native positive Support, causal history or Merge positive Support at every class entry.
Those remain genuine entry laws in the proposed Force theorem.
CurrentNative.At is a cap/origin law, not the new positive native Support.
ConstrainedCapMemoMerge.Stored is a conditional cap law, not MergePositivePosition.Support.
ParentPublicationHistory gives actual completed intervals for later causal composition.
Future actual class/edit adapters must retain the positive stores and the new slot law through their actual calls before this Force result can discharge that complete caller.

## Explicit bounds

This is a proposed completed-SAME-Force consumer and cache preservation theorem.
It does not cover unfinished Target/Fold cuts or failing internal Parent/Merge instructions.
It does not infer histories at old slot writers from current histories.
It does not prove whole-class positive ancestry, NormalizedChildSeparation.Rel, outer owner exclusion, renewed-query totality or global termination.
Opaque Mu input support remains subject to the explicit raw corridors and native cap premises.
No official source, old frozen package, Haskell, fixture, Audit or Git state is changed by this plan.
