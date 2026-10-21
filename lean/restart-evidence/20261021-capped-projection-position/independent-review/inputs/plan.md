# Selected class observations after native position support

Date: 2026-10-21 03:57 CEST. This is an unproved next-step plan. It adds no Lean jobs, proof pairs, or examples. It preserves the earlier class plan as a historical input. The native request law and later-heap operand law discussed as pending in that input now have checked producers. The source rebase is a separately checked 49-line candidate. Its exact bytes are included here; it was not installed at the official path when this plan was made.

## Smallest next theorem

Prove a capped inverse for ONE actual projection and selected complete read. It must handle a nonplain root row and a positive descendant of a plain row. For this plan only, write:

```text
RowPositive row [] := plain row.constraint = false
RowPositive row (i :: q) := exists child,
  row.children[i]? = some child and PositiveAt child q
```

This is notation for two explicit cases, not a proposed public relation. Retain these exact calls and indices:

```text
project : Project (path.map Int.ofNat) value before projected after
read    : Read projected reader rows readAfter
selected : rows[rowIndex]? = some row
relevant : RowPositive row residual

SemanticReady before, CostHeap before, Available before value
GuardHeap Plain before, Cap Plain depth value
SemanticReady reader, CostHeap reader, Keeps after reader
GuardHeap Plain reader
----------------------------------------------------------
PositiveAt value (path ++ residual)
```

No root-row index enters the natural child path. The root case includes nullary rows. The descendant case retains the same child index and complete row. Keep this theorem generic over the actual returned calls. Do not require a future projection or read to complete. A closedness premise is acceptable only if a reused cap endpoint needs it; the open exposure and indexed spine interfaces themselves do not require it.

The proof should follow `ProjectionReadSpine.project` and the actual read worklist. Ordinary steps use its exact source row, child, projected operand, read prefix and suffix. Union alternatives consume no natural child index. At a Mu step, `Cap Plain depth` forces hereditary Plain by constructor inversion. `ConstrainedCapOpenExposure.nodeEdges/head` and `RecursivePlainRead.project_read` exclude a relevant positive row from that region using the actual guard store. A union Head still needs its actual member provenance; it is not necessarily Plain as a whole. Reference reads can succeed only through the literal supported exposure rules. Do not replace an actual returned row with `nodeEdges (.mu ...)`, which is empty by definition.

`ConstrainedCapProjection.node` already derives the returned cap and store, but it does not derive a source position. `RecursivePlainRead.project_read` handles an entirely hereditary Plain input, not a finite ordinary prefix with positive rows. The proposed inverse is therefore a missing source law, not a wrapper around either endpoint. A small private Head/read inverse plus one public projection/read theorem should suffice. An estimated 180–300 additive lines is unproved; review the proof route before expanding it.

## SAME native continuation consumer

Apply `NativeRequestPositivePositions.call` to the actual `AllocatedTargetQuery.Step.run` trace recovered from the SAME leaf receipt. Keep its request, before state, returned value, after state, and captured writer unchanged. Its old `Return.result` contains `CheckedJointCode.NodeLaw`; instantiate that law at the supplied operand caps to derive the returned cap. The new capped observation inverse then maps the SAME remaining projection/read to a finite positive position in that returned value. Finally apply the OR-input conclusion of `call` at `path ++ residual`.

The result is `PositiveAt left (path ++ residual) or PositiveAt right (path ++ residual)` for that exact query and exact continuation. A leaf adapter can retain its already supplied full writer tuple. It must not call a writer selector or normalize a second unrelated native event. `ClassSelectedChildLineage.Selection.native` and `ClassEventExecutions.Source` already expose the exact actual trace and captured native return. Physical `Keeps` permits availability transport to a separate reader. It does not transport native memo history or reconstruct an internal writer-entry cache law.

Use the explicit `call` entry contracts at the actual query cut. The fixed-source cold `request` does not directly accept every later generated operand. At a completed query boundary, `ConstrainedCapCurrentNative.step` already derives current cap stores and captured origins from the same actual step. `NativePositiveSupportRebase.rebase` can move the new support to that current source using those SAME origins, actual growth and issued extension. It neither creates support for new cells nor supplies causal publication history. Additive current-query transport must install the positional law at actual protected finishes via `call`, then preserve or rebase it at genuine physical changes.

## One literal class, then chronology

For ONE actual `Class record phaseValues before memo results after saved` and its `ClassReads`, the bounded consequence should quantify the actual selected output slot, projection and read above. Under genuine entry support and finite caps for the participating captured values, derive:

```text
exists inputIndex input sourceSuffix,
  phaseValues[inputIndex]? = some input and PositiveAt input sourceSuffix and
  Rel E (outputIndex :: (path ++ residual)) (inputIndex :: sourceSuffix)
```

Here `Rel` is the existing `NormalizedChildSeparation.Rel`. Every executed record must have its actual paths contained in `E`. Do not assert congruence fixedness of a retained sublist. Ordinary reconstruction uses the same row guard and ordered child. At a leaf, the input arm keeps its path. The target arm chooses an actual competing path from `operandPaths record.paths editedPath`, then uses `Rel.member` with the SAME residual suffix.

The first class captures the prepared forest, so `TargetLaterHeapPositivePosition.operand` handles its actual later operand heaps from the original false gates. A later class captures literal `phaseValues` from the tail return. That theorem's prepared-forest argument cannot be changed to arbitrary `phaseValues` without a derived source law. `ClassPassPhaseLineage.fold_indexed/fold_phase` provide the exact tail, class, and later schedules. Resolve the head output into its captured tail forest, then compose the tail relation with `Rel.trans`.

At `EditNode.recursive`, first follow the actual body-edit induction. Only its input-source arm passes backwards through the actual Head to the pre-Head value. Its target-source arm retains its competing class path. The body edit can add a positive contribution to a Plain exposed input. The Head inverse must not be applied directly to that changed body-edit return.

Class-local target slots need a positional assertion derived at each actual first `Force.miss`. A `Force.hit` reuses that same assertion. `AllocatedSharedTargetState.SlotReceipt` preserves the actual historical target graph and forward interval, but it does not contain historical native position support. Do not recover that support backwards from the current cache. The existing `ConstrainedCapMixedShared.initial_stored/store_stored/force_receipt` pattern supplies actual slot/cap threading, and `ConstrainedCapMixedEdit.node` supplies caps relative to the captured forest and current input. Extend that local induction with the actual position result; do not assume the desired output ancestry as a public premise.

## Premise producers and limits

* Actual calls and chronology: `ActualClassSemanticReads.class_reads`, `ClassPassPhaseLineage.fold_phase`, `SharedEditChildLineage`, and `ClassObservationSpines` retain the selected edit and exact remaining continuation. The last module currently accepts only a nonplain root row. Positive descendants require the two-case relevance extension above.
* Physical support: projection/read effects derive semantic readiness, costs, availability and forward Keeps at their literal cuts. `LowerGuardHeapReturns` derives the guard store through actual successful class operations. Heap growth alone does not certify new Mu records.
* Causal Mu history: `RequiredPublicationHistory.head/read/project` and `ParentPublicationHistory` compose actual physical intervals; `NativePublicationTrace.from_history` covers actual native traces. These histories differ from native memo writer history. No arbitrary reader gap has a history merely because it has Keeps.
* Native caps and support: finite caps are explicit restricted inputs. Mixed edit/target producers propagate their own actual bounds. The new support law starts from empty native tables or genuine current Support, and rebase additionally requires actual captured Origins. Availability or a source-started heap alone does not supply either cap or Plain binding support for arbitrary generated operands.
* Original gates: `OuterSupportedParentHistory.selected` retains the SAME historical Parent writer's scan, Required call, support, normality and guard store. `RequiredForestPositive.requireAll` and the later operand theorem use false traces on the ORIGINAL forest at the original scan heap. They do not produce a false trace on prepared or changed phaseValues. Replaying a trace through a larger heap does not change its value argument.

The finite-cap observation inverse is not a solution for the unrestricted class theorem. The checked opaque-Mu counterexample still has no finite positive input path while an actual result has one. `GuardHeap Plain` equates profiles; it does not assert that all Mu bodies are Plain. For the unrestricted selected-class statement, retain actual `ClassObservationSpines` native/Head cuts and `RecursiveEventPublications.fold`'s SAME event, occurrence, Entry site, supported observation and full-row PathOrigin. That endpoint supplies causality, not the missing positive transfer law. `RecursiveSourcePlain.required` excludes the original recursive corridor only where actual Required Origin and the ORIGINAL false gate apply. No theorem yet transfers that exclusion to every changed phaseValues corridor.

A minimal nonvacuous bounded fixture for the proposed inverse should select a positive descendant under a plain ordinary row, with an actual union read and a Plain Mu alternative. It must retain the exact natural child index and both read heaps. A plain root-only fixture would miss the needed descendant case. A later full class fixture must use its actual captured phaseValues and a warm target hit. No fixture or Lean check is run for this plan.

Selected observation transfer, positional slot threading, unrestricted opaque-barrier preservation, original-field key exclusion, renewal, termination and Haskell refinement remain open. No finite path relation or source publication chronology is asserted to be a global runtime rank.
