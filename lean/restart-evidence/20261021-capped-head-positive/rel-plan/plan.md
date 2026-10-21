# One completed class: positive ancestry under the same record

Status: SOURCE-ONLY PLAN. No new Lean command, public proof pair, or implementation.
Review time: 2026-10-21 06:02 CEST.

The next result should trace every literal positive position in the returned forest to the literal forest captured by this class. It should use `SourceCurrentNormalizedChildSeparation.Rel [record.paths]` on whole natural forest paths. It should retain the same completed `ClassReads`, checked states, Merge states, and global memo bundle. The relation needs no normalization fixed-point premise. Its `member` constructor already retains a common suffix. The later `single` and `child_separate` results have stronger premises and serve a different task. [R1]

## Exact proposed public endpoint

Add one `class_reads` theorem in a new module, provisionally `SourceCurrentClassPositiveAncestry`. Keep the literal arguments and premises of `SourceCurrentClassEndpointCorridors.class_reads`, including its actual `ClassReads`, coherent nontrivial record, original captured values, readiness, admission, selected-path domains, physical Merge store, language coverage, memo validity, current cap/origin store, Merge cap store, and raw selected masks. Add only these three genuine entry laws:

```lean
(supported : SourceCurrentNativeRequestPositivePositions.Support
  before.native.machine.heap before.native)
(causal : SourceCurrentNativeMuPublication.History
  empty before.native.machine.heap)
(positiveMemo : SourceCurrentMergePositivePosition.Support memo)
```

Return the existing class receipt and forward corridor conclusion, plus the derived stores and the new backwards law. The following is the exact intended conclusion shape. `Current`, `MergeStored`, `RawCorridor`, `PositiveAt`, and `Rel` denote the existing public predicates; they do not denote new supplied result laws.

```lean
∃ next,
  SourceCurrentAllocatedClassEdits.Receipt formulas solver next
    record values before memo results after saved memos final ∧
  Current after ∧ MergeStored saved ∧
  All₂ (fun original result => ∀ signedPath,
    RawCorridor signedPath original → RawCorridor signedPath result)
    values results ∧
  SourceCurrentNativeRequestPositivePositions.Support
    after.native.machine.heap after.native ∧
  Nonempty (SourceCurrentNativeMuPublication.History
    empty after.native.machine.heap) ∧
  SourceCurrentMergePositivePosition.Support saved ∧
  ∀ outputIndex result, results[outputIndex]? = some result →
    ∀ residual, PositiveAt result residual →
      ∃ inputIndex originalPath original,
        values[inputIndex]? = some original ∧
        PositiveAt original originalPath ∧
        Rel [record.paths] (outputIndex :: residual)
          (inputIndex :: originalPath)
```

This theorem concerns a completed class supplied by its actual `ClassReads`. It does not construct a future class return. Its captured `values` are exactly the entry values of that class. The source graph creates its target slots with `initial before memo`; only those slots start empty. The native tables and Merge table remain warm. [R2]

The existing public endpoint may supply its receipt and forward corridor relation on the same `reads`. The new joint induction must derive the additional stores and backwards law. No receipt or hidden writer identity needs to be unique. No caller supplies a positive-output callback, `Rel` witness, target ancestry law, or future completion premise. [R2, R3]

## Head adapter identified by this audit

The private `CappedProjectionPositivePosition.head_positive` is not accessible as a reusable public endpoint. Do not reference its generated private name. A small additive public adapter, provisionally `SourceCurrentCappedHeadPositivePosition.head`, can expose this exact contract:

```lean
{value exposed before after path}
(actual : SourceEqualityRequiredHead.Head value before exposed after)
(semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
(costs : InternedFreshOrdinaryCostHeap.Heap before)
(available : Available before value)
(guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain before)
(depth : Nat) (bounded : SourceCurrentConstrainedCap.Cap Plain depth value)
(positive : PositiveAt exposed path) : PositiveAt value path
```

This package does not implement or compile the adapter. At 06:01 the separate author supplied a source-frozen 60-line candidate, SHA `f34430290bf3cbf04cbbbf590779fd52c0bb6abd8e09f6d85735d33995e5dfb8`, with reported successful first strict and FULL runs. At 06:03 the author confirmed its 29-pin package frozen and both verifiers successful. I read all 60 lines. The source implements the exact contract and reuse route below. Its source is pinned separately as a candidate input; no author receipts or public proof pair are counted by this plan. Official availability and author-package verification remain separate. It needs no closure, desired row provenance, input `Plain`, causal-history premise, or future read. [R4, C2]

1. Unpack `actual` once as `Head.read fuel rows middle exposedRead rebuilt`. This gives the actual `Read.done fuel exposedRead` of `value` at `before`.
2. Use `ProjectionCosts.read_effects` to derive the actual middle semantic facts and resident rows. Use `EqualityLeafProjectionPhysical.makeNode_edges` and `RequiredCache.node_ordinary` on the same `rebuilt` equation. Thus every selected row in `exposed` is one of the actual read rows. Canonicalization can remove a row or a duplicate. It cannot introduce a different row.
3. For `PositiveAt.root`, recover an actual raw read index with `List.mem_iff_getElem?`. Apply public `CappedProjectionPositivePosition.root` with `Project.root`, the same `Read.done`, `path := []`, `reader := before`, and reflexive `Keeps before before`. Use the entry semantic, cost, availability, guards, and cap. Do not read the final heap in place of the actual read entry.
4. For `PositiveAt.child`, keep the same selected row, child index, child, and positive residual. Apply public `CappedProjectionPositivePosition.child` with the same zero-path project and read. Rewrite `[] ++ childIndex :: residual`.
5. A returned union-positive case contradicts the actual ordinary result. The adapter does not clone the collector, read induction, Mu reconstruction, or exposure framework.

The actual candidate has 60 lines including imports, aliases, and comments. Its only public endpoint is the contract above. The class implementation should reuse that endpoint after promotion. This plan does not treat the existing private proof as public and does not claim to prove the adapter itself. [R4, C2]

## Smallest joint class induction

Use the existing mutually indexed `NodeReads`, `ChildrenReads`, and `RowsReads`; wrap `ListReads` once. Preserve their actual chronological states. Keep helpers private. No new evaluator, generic execution framework, or public result predicate is needed. [R5]

For a subtree at absolute natural address `a`, use this private backwards postcondition:

```lean
∀ q, PositiveAt result q →
  PositiveAt input q ∨
  ∃ i sourcePath source,
    values[i]? = some source ∧ PositiveAt source sourcePath ∧
    Rel [record.paths] (a ++ q) (i :: sourcePath)
```

This disjunction is an induction conclusion, not a caller premise. The left arm is the same local input at the same residual. The right arm already names a literal root in the fixed class capture. At the forest root, the left arm gives the same input index and `Rel.refl`. The right arm already gives the requested whole-forest relation. A separate arbitrary input-ancestry premise is not necessary.

Track actual child offsets. `ChildrenReads` begins at `offset` and advances it by one. Its private postcondition should retain exact same-index source/output lookups, with each child's address `a ++ [offset + localIndex]`. Row alternatives do not add a component to the child path. Keep output row index, source row index, and child index distinct. For `RowsReads`, retain an ordered source/output row relation with equal full guards and the indexed child postconditions. Actual `makeEdge_fields` proves those equalities, including warm constructor winners. [R5, R6]

Also retain placement of each compiled leaf: an actual retained relative signed path is the natural path below `a`, and its action token is exactly that complete natural address. Derive this from `compiled_disjoint`, `build_leaves`, and the literal compiler `edits record.paths id`. Do not replace token equality with mere token membership. `Allowed` supplies record membership; it alone does not identify the leaf's current address. [R7]

Carry at every actual cut:

- The existing `Ready`, available values or rows, edit-domain safety, global memo validity, and fixed captured `Values` and masks.
- `RequiredSharedTargetCap.Stored`: current native cap/origin store, Merge cap store, and caps for every present class slot.
- Native positive `Support` at that cut's current heap, causal `History empty currentHeap`, Merge positive `Support`, and the per-present-slot backwards law from the force theorem.
- Input corridors at each retained compiled leaf. These produce the leaf input cap and the recursive Head input cap. They are not backwards positive ancestry certificates.

The private induction has these actual cases:

| Case | Positive position and store action |
| --- | --- |
| Leaf | Unpack the same leaf `Reads.apply forced query`. Call the new slot `force_receipt` on `forced`; use `forced.present` to instantiate the derived same-slot law. Obtain a finite input cap from the leaf's empty residual corridor and a target cap from the returned slot store. Call `NativeCurrentPositivePositions.step` on `query.actual` with the same depth-max caps and closed/available operands. Its same-`q` OR gives local input or target support. For the target arm, recover the actual natural competitor from `operandPaths`. Use `Rel.member record.paths` with the exact leaf token, that competitor, and the same suffix `q`. The source positive path is `competitorTail ++ q`. |
| Empty | PositiveAt has no constructor for Empty. Retain stores and history. |
| Ordinary node | Use actual normalized `makeNode` membership to select a rebuilt row. Match it to its source row through the ordered row relation. A root-positive guard transfers by full guard equality. A child-positive position keeps the same child index and uses that child's induction conclusion. Lift inherited child support with `PositiveAt.child`; associate list appends for a captured-source result. Do not assume canonical output row index equals source row index. |
| Recursive Head | `HasLeaf` and the actual input leaf corridor imply a finite cap for the whole recursive input: `RawCorridor.node` would require an ordinary node and contradict the recursive constructor. This is the existing endpoint420 route. Derive the actual exposed cap with public OpenExposure.head, then make every exposed-body leaf corridor full. Use the body IH at the same address. Transfer its local-input arm through the missing Head adapter above. Its captured-source arm needs no additional transfer. |
| Child scan | Preserve unselected positions literally. In the selected branch run the first IH, then supply its actual returned stores/history to the tail IH. The next child's address uses the recorded incremented offset. |
| Row scan | Run child IH, perform the actual raw edge constructor with retained full guard and ordered children, then run the later rows with that exact returned state. Do not reconstruct an independent row execution. |
| Forest list | `compiled_children` excludes a list-root leaf. Apply the child law to the actual list graph. The same-index inherited source proves the public reflexive branch. |

The existing endpoint420 source is a proof pattern for placement, cap-store threading, recursive finite-input discovery, and physical effects. Its `Preserves` conclusion does not imply the new backwards law. Reuse public effects and existing public endpoints. Copy only the small private placement/finiteness steps needed by the new induction. An initial estimate is 300–500 lines for the class proof including the small Head adapter and explicit dependent cases, not another exposure framework. [R3, R5, R7]

## History and warm-store obligations at the same cuts

The new slot theorem returns genuine causal publication history and both positive stores at its actual force return. The leaf query then uses `NativeCurrentPositivePositions.step` at that exact state; its result contains rebased Support and causal history for the same query return. A cap theorem alone does not establish either positive store. [R8]

Constructor-only node/edge work and Head work do not change the complete native node or edge tables. Use the exact physical extension and final Good facts with public `NativePositiveSupportAdvance.advance`; use `CurrentNative.advance` with the actual final semantic/guard facts for the old cap/origin store. Merge and target-slot tables remain literal through `advanceHeap`. Do not derive a new cell law from growth alone. [R9]

For causal history, use public `RequiredPublicationHistory.head` at the actual Head and append its interval to the incoming empty-to-entry history. For pure constructors use `History.retain` with its required actual `NoNewMu` proof: `makeNode_noNewMu` for a node and literal unchanged `nodeRecords` for an edge. Growth and issued retention alone do not construct this history. Public `ParentPublicationHistory.node/children/rows/list` also derives the interval for the same completed graph; it does not require the desired positive result. These are physical Mu publication histories. They are different from the `NativeEdgeWriterGrowth.History` premise in class observation spines. [R10]

Initially the class-local slot ancestry predicate is vacuous because `initial.targets = fun _ => none`. The initial native and Merge positive stores are not vacuous merely because class slots are empty. They remain explicit public premises. The new completed-class endpoint should return their derived final versions so a later actual class fold can pass them to the next capture. Current corridor chronology only returns cap stores and forward corridors; it does not already supply these positive stores or causal history. [R2, R8, R11]

## Missing producers and exact limits

The remaining class proof work is the joint completed-class positive/store induction. It depends on official availability of the separate new Head inverse adapter. The new slot law supplies the actual leaf target branch. No separate class/native evaluator or general read-exposure framework is missing. No finite-set cardinality result is needed for this step. The proposed class theorem and its private induction remain unproved.

The public observation-spine theorem is not a substitute: it requires an original false gate, Required Origin, and a native writer History, and its `true` branch explicitly stops at an actual native leaf or Head. Use its exact reconstruction/read patterns as prior art. Do not claim that it already closes those stops. [R12]

Do not generalize the conclusion to a partially failed class, an unfinished Parent, or a future outer return. A proof about a completed child graph at a cut does not prove that an unfinished enclosing class preserves positive support. Do not infer warm native/Merge positive laws from physical `Stored`, language coverage, finite caps, or current heap growth. [R8, R9]

This one-class result does not prove a common original anchor for two distinct positive paths. The returned existential witnesses can differ. It does not prove active-owner exclusion, retained child equality classes, well-founded renewal, native or outer termination, or Haskell refinement. Later chronology can compose actual relations under the original normalized class family, but needs its own source-grounded store/history and relation-membership proof. The fixed-point and dropped-class premises of `child_separate` remain separate obligations. [R1, R11]

## Source references

All references name exact snapshotted ROOT-relative sources in `source-pins.json`. The slot proof has the same bytes in its draft directory and official source at review time; its separate draft pin preserves this observation without claiming owner-package freeze.

- R1: `SourceCurrentNormalizedChildSeparation.lean` 14–24, 87–97, 118–145.
- R2: `SourceCurrentAllocatedClassEdits.lean` 30–50, 58–118; `SourceCurrentAllocatedSharedTargetState.lean` 28–77.
- R3: `SourceCurrentClassEndpointCorridors.lean` 28–36, 180–198, 201–279, 382–418.
- R4: `SourceEqualityRequiredHead.lean` 15–20; `SourceCurrentCappedProjectionPositivePosition.lean` 142–180, 244–261; `SourceEqualityProjectionCosts.lean` 20–60; `EqualityLeafProjectionPhysical.lean` 17–33; `SourceEqualityRequiredCache.lean` 73–82; `SourceEqualityProjectionGraph.lean` 22–32.
- R5: `SourceCurrentAllocatedSharedEditGraph.lean` 30–80, 97–175; `SourceCurrentClassEndpointCorridors.lean` 201–378.
- R6: `MergedPhysicalGroupEdges.lean` 26–38; `EqualityLeafProjectionPhysical.lean` 17–51; `SourceCurrentRequiredPositivePosition.lean` 25–40.
- R7: `SourceCurrentAllocatedClassEditPlan.lean` 17–79; `SourceEqualityEditCompiledPaths.lean` 66–78; `SourceCurrentClassEndpointCorridors.lean` 78–106.
- R8: `SourceCurrentRawCorridorSharedTargetPositivePositions.lean` 28–48, 223–267; `SourceCurrentAllocatedSharedTargetForce.lean` 76–93; `SourceCurrentNativeCurrentPositivePositions.lean` 24–79.
- R9: `SourceCurrentNativePositiveSupportAdvance.lean` 19–33; `SourceCurrentConstrainedCapCurrentNative.lean` 27–54; `SourceCurrentAllocatedSharedEditGraph.lean` 25–28; `SourceCurrentAllocatedSharedEditEffects.lean` 90–147; `SourceCurrentConstrainedCapMixedEditStoreEffects.lean` 32–89.
- R10: `SourceCurrentRequiredPublicationHistory.lean` 119–138; `SourceCurrentParentPublicationHistory.lean` 147–165, 217–237, 274–328; `SourceCurrentNativeMuPublication.lean` 86–98 (`History.retain` and `History.trans`).
- R11: `SourceCurrentClassCorridorChronology.lean` 72–104, 106–156, 158–195.
- R12: `SourceCurrentClassObservationSpines.lean` 640–729, 954–986.
- C2: Separate candidate `SourceCurrentCappedHeadPositivePosition.lean` 26–58, preserved under `inputs/candidate-head/`; the candidate pin is independent of the ROOT foundations and does not claim that this package ran Lean.
