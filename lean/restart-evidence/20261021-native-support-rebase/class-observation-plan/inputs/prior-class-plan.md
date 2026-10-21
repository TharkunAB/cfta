# Chronological class positive-position support

Date: 2026-10-21 03:17 CEST. This is a source-only plan. It has no new Lean jobs or proof pairs. Every theorem proposed below remains unproved.

## Result and smallest next step

The new Target operand theorem closes projection plus Merge at the initial prepared heap. It does not close a class fold. Two distinct transitions remain: the heap changes within a captured class, and the captured forest changes between classes.

The smallest useful next producer is an actual later-heap operand law for the SAME prepared forest. It should take the actual Required return, original false class traces and actual operand equation, but replace the exact prepared-heap equality by actual forward Keeps plus current semantic/cost/causal-guard support. The public `TargetOperandPositivePosition.project` already permits the projection to start at an arbitrary supported heap. Its initial false gate and UnionNormal name only the original scan heap. This next producer needs no prepared false gate or new original-to-prepared identity.

A complete actual-class source relation then needs an observation-support step across earlier class edits. A finite positive-position native OR law helps at actual intersections, but it does not by itself justify this observation-support step through opaque Mu values. The proof must retain and resolve actual Head/native continuations or prove a sufficient recursive cap invariant.

## Actual order and fixed objects

`SourceCurrentAllocatedClassWorker.fold` executes the tail classes before the head. The head's `runClass` captures the literal tail-return forest. `SourceCurrentClassPassPhaseLineage.fold_indexed/fold_phase` exposes the exact tail, head and later schedule, together with phase effects and histories. Thus a later class uses `phaseValues`, not the initial Required result by definition.

Within ONE `runClass`, its `values` parameter is fixed. `AllocatedSharedEditGraph.EditNode/EditChildren/EditRows` thread changed heap, memo and local slots through ordered edits while their `originals` parameter remains this captured forest. `AllocatedSharedTargetForce.Force.miss` constructs the target from that captured forest. It does not project the partially edited output. A hit returns an earlier exact slot value.

`SourceCurrentAllocatedTargetGraph.Fold.cons` executes the head operand, then the remaining fold and then the native query on the head and tail values. `Target.nonempty` uses the first path as seed. Therefore even one target can project its fixed captured forest at several different heap prefixes. Later target forces can start after earlier leaf queries and constructor work.

Across classes, the next class captures the actual changed tail-return forest. `AllocatedClassEdits.Receipt.transport` and `AllocatedClassPass.Receipt.transport` preserve path domains. They do not state Required Origin, forest identity, positive support or a false gate for that changed forest.

## Proposed later-heap operand contract

Use the same original and prepared forests and the same literal equations as the new operand theorem:

```text
requireAll requiredFuel requiredReadFuel (SelectedRequired.paths selected)
  originals scanHeap = done prepared preparedHeap

TargetWorker.operand p h m s ((index :: path).map Int.ofNat)
  prepared current memo = done result after saved
```

Keep the initial scan contracts SemanticReady, UnionNormal, CostHeap, Values and GuardHeap Plain. Keep the actual original false ClassTrace for every selected record, the chosen record membership and `index :: path` membership. Keep current physical Stored and Merge Support. Replace `current.heap = preparedHeap` by:

```text
Keeps preparedHeap current.heap
SemanticReady current.heap
CostHeap current.heap
GuardHeap Plain current.heap
```

Then retain the existing exact result:

```text
Support saved /\ exists original,
  originals[index]? = some original /\
  PositiveAt original (path ++ residual)
```

Current availability of prepared values follows from Required effects and Keeps. Current semantic/cost support follows from Ready/Good at the actual prefix. The current guard invariant must follow through the actual operations; Grows alone cannot create its certificates for new Mu records. `SourceCurrentLowerGuardHeapReturns.operand/target/force/leaf/edit/run_class/class_fold` provide the actual-success transport route. `SourceCurrentOuterMergePositionSupport` provides the corresponding Merge law; its completed-call boundaries must remain explicit. `SourceCurrentUnionNormalEdits` and the existing scan endpoints already preserve normality, but current normality is not a new prerequisite of the reusable projection theorem.

Implementation route: factor or repeat the short literal projection/Merge inversion, reuse `project`, and derive current prepared availability by Keeps. No change to the original gate, Required Origin or private safe-projection proof is needed. Estimate: 50–90 additive lines, with a small private actual-operand helper if it removes repeated inversion. This is a real applicability extension, not a new class result.

## Exact class/fold source conclusion

Use forest positivity only as notation in this plan:

```text
FPos values (index :: suffix) :=
  exists value, values[index]? = some value /\ PositiveAt value suffix
FPos values [] := False
```

No new public hierarchy is proposed. The actual final theorem should consume the actual selected scan/Required/pass schedule and its entry support. Its positive conclusion is:

```text
forall outputIndex value suffix,
  results[outputIndex]? = some value -> PositiveAt value suffix ->
  exists inputIndex original sourceSuffix,
    originals[inputIndex]? = some original /\
    PositiveAt original sourceSuffix /\
    NormalizedChildSeparation.Rel E
      (outputIndex :: suffix) (inputIndex :: sourceSuffix)
```

Take E as an ambient original equality-class list that contains every executed record's paths. A core theorem can use `E = kept.map Record.paths`; a later normalized consumer should embed it in the actual normalized own classes. Do not assert that the selected sublist itself is a congruence fixed point. The actual precheck orders original OWN records. The combined own/inherited normalization is used for rejection, rather than replacing those scheduled records. `SourceEqualityPhysicalClassEntry.live_records` and the positional retained-record APIs expose this distinction.

At an actual edit leaf at source path `left`, a positive result can come from its current input or from its class target, subject to the justified native law. The input arm retains the same path. A target arm identifies an actual competing operand `right` from `operandPaths record.paths left`. Each competing path belongs to the same original record. It gives exactly:

```text
Rel.member record.paths recordInE left right leftIn rightIn suffix
  : Rel E (left ++ suffix) (right ++ suffix)
```

The SAME suffix is essential. The new operand law provides `FPos originals (right ++ suffix)` when its captured forest is still the prepared forest. No row index is added to this child path. Literal union alternatives add no child component. Different forest slots can occur in different class members; the final source forest index is not asserted equal to the edited output index.

Ordinary row reconstruction must retain the actual ordered child index and full original guard. The nullary case contributes a root positive guard only. Empty propagation either retains values or erases them to Empty, so it cannot add a positive occurrence. Chronological class folds use Rel.trans in execution order: first resolve the head output into its actual captured tail forest, then apply the tail source relation. The pure `NormalizedChildSeparation.single/child_separate` lemmas apply after this execution law, with their explicit congruence fixed-point and per-child drop hypotheses.

## What the actual class proof must maintain

For one captured class, derive a local slot assertion when the first actual Force.miss returns. For each stored target and residual suffix, its positivity comes from one actual competing path in the fixed captured forest, with the same suffix and actual native/operand evidence. Force.hit then reuses that assertion. This assertion starts vacuously because runClass clears target slots. It must be threaded with actual effects; current Merge Support does not imply Support at an independently selected historical slot writer.

`AllocatedSharedTargetState.SlotReceipt` retains the earlier actual Target graph, reads, receipt, forward Keeps and memo extension. It retains availability and language inclusion. It does not already retain the new positive law or all historical support premises. One can derive the local assertion while following the actual first write and preserve it through hits. This avoids assuming desired ancestry for a warm slot.

A single captured-class proof can use actual mutual EditNode/EditChildren/EditRows induction. Preserve the original full row fields at ordinary constructors. At leaf queries consume a native law for THAT actual request/writer and the same operand support. A proposed finite native contract is:

```text
actual Step left right before result after -> justified entry contracts ->
  forall suffix, PositiveAt result suffix ->
    PositiveAt left suffix \/ PositiveAt right suffix
```

This is an unsolved scoped native contract, not an axiom to add. The unrestricted version is refuted by the existing actual source-built, empty-native-table opaque-Mu counterexample. Closedness, available operands, Good, causal publication alone and empty tables do not repair it. The necessary cap/binding/source conditions must be derived at the SAME actual request, including warm writers.

## The additional observation obligation

Finite PositiveAt treats Mu and references as opaque. The edit graph has a real recursive constructor: it runs Head and then edits the exposed ordinary value. A stored Mu can have no finite PositiveAt path while an actual Head exposes a nonplain ordinary row. GuardHeap Plain records equality of body/probe guard profiles; it does not require either profile to be plain. Therefore finite positive support between phase forests does not justify arbitrary later projections or Head calls.

The original false scan gates exclude this contribution only on the original selected corridors. Required Origin transfers those initial corridors. It is invalid to apply safe_gate again to changed phaseValues or to infer that later values have the original Required Origin. Replaying an original false trace through heap growth changes its heap, not its value argument.

For the actual class/fold proof, strengthen the PRIVATE induction to selected observations. At each tracked selected path `r`, retain a law for actual supported forest Project r followed by a positive residual occurrence. Resolve it to original FPos with Rel E `(r ++ residual)` sourcePath. At the initial prepared forest, the new project theorem and Required origins prove this law. It is an induction invariant derived from actual preceding class edits, not a desired source law supplied by a public caller.

The native event branch of this stronger induction needs a continuation-aware support proof: it must handle the remaining actual Project/Read of the SAME native return, or derive recursive plain/cap facts that rule out its relevant Head branch. The finite OR-input statement alone does not handle that continuation. It is not enough to choose an unrelated prior native event with the same row guard or body. `SourceCurrentClassObservationSpines.node` retains exact selected projection/read frames and native/Head cuts. `ClassFoldRowOrigins` and `ClassFoldRecursiveValueOrigins` retain actual events and chronology. These are reusable causal receipts, but none is the missing complete positive-observation transfer theorem. The old observation endpoint also accepts only a root nonplain read row; the new positive-child relevance change would be needed when extending it to this observer.

This is a proof-contract obstruction, not a new checked execution counterexample to the intended selected class theorem. The old opaque-Mu fixture establishes the unrestricted native boundary separately.

## Supported Parent use and next sequence

`SourceCurrentOuterSupportedParentHistory.selected` calls edge_call once and keeps the SAME literal historical Parent writer, its entry Support/UnionNormal/GuardHeap Plain, actual scan, Required, pass and original false gates. It supplies the correct initial source for this pipeline. It does not identify that writer's prepared forest with every later phase forest or supply the native observation law.

Recommended bounded order:

1. Add the later-heap actual operand producer. Verify the arbitrary supported prefix with actual GuardHeap and Merge Support; do not add a prepared false gate.
2. Prove actual Target Fold plus class-local slot positive support, using a separately proved scoped native primitive/request law at each actual request. For the first chronological class, the fixed capture is exactly prepared, so step 1 supplies its projection law. For later classes, this step can be an internal lemma only under the selected-observation induction established in step 3; it does not derive a fresh source law for arbitrary phaseValues. A rough estimate is 140–240 lines after the operand adapter and native law exist.
3. Extend the actual observation/class induction to relevant positive child rows and SAME native/Head continuations. Derive the private selected-observation invariant across actual phaseValues. A first full version likely needs 400–700 lines because old causal spine details are private; no global framework is justified yet.
4. Fold the resulting source relation chronologically, attach Required support once, and apply normalized geometry. Do not infer earlier-writer support from current Support, normalized fixedness from retained sublists, or a global rank from the finite Rel chain.

No proof is claimed for steps 1–4 here. No theorem source, Haskell file, Audit file or current documentation was changed. No Lean, Lake, runtime or constructed-example job was run for this plan.
