# Next quantitative outer returned-cell theorem

Date: 2026-10-16 23:17 CEST.

The next result must certify each actual completed outer owner. Retaining the lower native and Merge guard stores through all eight families does not supply a quantitative profile of a warm outer return.

## Proposed certificate

Use a separate new universal certificate, alongside the existing domain and height store. A concrete proposed namespace is `SourceCurrentAllocatedFiniteOrdinaryOuterProfile`. Define pure output transformers before defining the store. The following types specify their role. They are a proposal, not declarations already proved.

```lean
NodeCertificate (owner : PartialState.NodeRequest) (result : Value) : Prop :=
  ∀ rows arity heightLimit guards,
    NativeProfile.NodeShape rows arity owner.value →
    GuardProfiles.Node guards owner.value →
    height owner.value ≤ heightLimit →
    NativeProfile.NodeShape
      (nodeRows rows arity guards heightLimit)
      (max arity 1) result ∧
    GuardProfiles.Node (nodeGuards rows arity guards heightLimit) result

EdgeCertificate (owner : PartialState.EdgeRequest) (result : EdgeValue) : Prop :=
  ∀ rows arity heightLimit guards,
    NativeProfile.EdgeShape rows arity owner.value →
    GuardProfiles.Edge guards owner.value →
    edgeHeight owner.value ≤ heightLimit →
    NativeProfile.EdgeShape
      (parentRows guards rows arity heightLimit)
      (max arity 1) result ∧
    GuardProfiles.Edge (parentGuards guards) result
```

The edge certificate concerns EdgeCall, whose body is the local parent reduction. Descendants run afterward and have a separate edge-output conclusion. The owner retains its complete inherited value, but these profile bounds need no inherited-size parameter. The processed classes are the ordered own records. The existing domain and height certificate remains separate and supplies actual height narrowing. Combining these conclusions in one returned-cell structure is also valid if the proofs still derive each component.

A proposed `Stored state` has two fields: every literal returned node cell satisfies NodeCertificate for that cell's stored owner; every literal returned edge cell satisfies EdgeCertificate for that cell's stored owner. Initial cold outer tables derive this predicate. Publication and demand introduce no returned value. Lower advance leaves both complete outer tables unchanged. Finish requires the actual evaluating cell equation and the local body certificate. It installs only that owner's law.

## Source-grounded transformers

For a parent with common original vector G, the new own theorem bounds classSteps by `2 * GuardOwn.classBudget G`. The candidate parent guard transformer is therefore:

```lean
parentGuards G := GuardTarget.foldLimit G (2 * GuardOwn.classBudget G)
```

It retains G and covers the class-pass child guards and original parent guard. Top and Empty sentinels also fit it. ParentUniformNumbers already gives `parentRows G R C H` and the arity ceiling `max A 1` when `C ≤ A`. Instantiate C with A for a common edge shape. Do not add a bound on the inherited payload.

Define the node transformers by height. Base height zero permits only Empty in the ordinary domain. For height H+1, bound each original row's EdgeCall using the parent transform at child-height H. Then process that returned edge's children using the smaller node transform at H, with the produced parent row, arity, and guard envelopes. The final raw edge keeps the returned parent guard and actual child positions. The final node keeps at most its original row count. Use explicit joins/maxima to retain the original row/vector bounds where required. Prove each transform retains its input and is monotone in the parameters that its composition widens.

This decreases the ordinary height even though row and guard envelopes can increase. It does not assume a finite key carrier. `PartialActiveOrder.lean:30–55` already separates node and edge ranks and ignores inherited identity. Existing Returned.Stored gives actual edge-height narrowing for warm hits, which is essential before recursive descendants.

## Needed producer before the cell lifecycle

The first missing proof is an actual supplied-read row/arity producer through Target, Force/Leaf, Edit, ClassPass, and Parent that needs no conservative resource headroom. Native OutputStored and MergeProfileCache already carry universal local profiles, so the proof can follow the new guard producer pattern at the same actual receipts. A resource completion theorem with sufficient initial capacity is not a verifier for every supplied completed prefix: a particular completed run can fit even when a conservative worst-case reservation does not fit.

Proposed immediate endpoint:

```lean
parent_profiles_from_reads
  (reads : ParentActual.Reads formulas solver actual memos final)
  (initial legitimate Context/Ready/At and old structural stores)
  (nativeOutput : OutputStored before.native)
  (mergeProfiles : MergeProfileCache.Stored before.merge)
  (nativeGuards : GuardStored before.native)
  (mergeGuards : MergeGuardCache.Stored before.merge)
  (inputShape : NativeProfile.EdgeShape R A original)
  (inputGuards : GuardProfiles.Edge G original)
  (heightBound : edgeHeight original ≤ H)
  (actual reached machine checks where the existing verifier needs them) :
  final lower stores ∧
  NativeProfile.EdgeShape (parentRows G R A H) (max A 1) result ∧
  GuardProfiles.Edge (parentGuards G) result
```

All final properties must be derived from those exact reads. No returned profile, enclosing completion, future capacity, or desired callback law can be an input. The actual lower read chain is needed to initialize class slots and derive each prefix's readiness. Only after this theorem is available should the outer producer install its EdgeCertificate.

## Exact warm-owner lifecycle

The current requests and keys are in `PartialState.lean:34–49`. Complete requests retain inherited payload and value. Keys retain inherited identity and physical value identity. The key is not the quantitative certificate.

At a warm node or edge hit, use current Sound and its linked cell to recover the actual owner and its input residency. Then use coherent complete-record identity to prove `owner.value = candidate.value`. `FiniteOrdinaryOuterState.lean` already implements this pattern in `node_evaluate`, `edge_evaluate`, `Stored.node_ready`, and `Stored.edge_ready`. `FiniteOrdinaryReturned.lean` has corresponding `Stored.node_hit` and `Stored.edge_hit` examples. Instantiate the stored universal certificate with the candidate's initial profile only after this equality is derived.

For a miss, use `PartialCallSteps.node_start/edge_start` to obtain the literal evaluating owner and running Context. Apply the actual smaller body read induction hypothesis for every initial profile parameter. Protect the same handle through the body with `PartialFrames.node_body/edge_body` and `Protocol.of_valid`; then finish using the preserved cell equation. The existing implementation is at `FiniteOrdinaryOuterActual.lean:158–170` and `:190–202`. This avoids a supplied body-law oracle and avoids installing a candidate law at an unrelated owner.

The pure lifecycle helpers can mirror the existing Returned module, but they are not the main result. The required main producer follows all eight actual strict read families and derives each new body certificate. Separate lower native/Merge storage retention is insufficient for that theorem.

## Execution order and remaining goals

`PartialGraph.lean:85–117` fixes the recursive order: edge call, descendants of its returned edge, then the original row suffix. Descendants combine inherited first with the returned edge's own field once, then use indexed descent for each actual child. The raw same-arity edge rebuild keeps that returned raw guard. Ordinary node reconstruction follows the completed row list. A quantitative proof must follow this order and use profiles at each literal returned state.

After profile certificates are produced, cumulative constructor Work still needs a separate all-eight recurrence and actual trace proof. It must pay for generated descendant occurrences and retained warm hits according to the literal schedule. Initial headroom must then imply each reached ParentInitialCapacity and the root numeric Plan before that parent completes. Profile bounds alone do not establish those reservations.

General Mu progress, selected recursive narrowing, solver work, equality allocation and normalization costs, signed constraint conversion, frontend correspondence, and concrete GHC/HashMap behavior remain separate full-library obligations. This proposal makes no new Haskell defect claim.
