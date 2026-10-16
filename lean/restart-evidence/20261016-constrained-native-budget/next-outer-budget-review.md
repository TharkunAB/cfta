# Next: returned profiles and cumulative outer capacity

Reviewed 2026-10-16 19:09 CEST. This is a read-only design review. It adds no proof, source change, or build claim.

## Established starting point

`lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryNativeBudget.lean:30–37` computes `nodeBudget` and `edgeBudget` from the literal original operands. `node_prefix_budget` at line 42 and `edge_prefix_budget` at line 94 bound constructor requests and both constructor supplies at **every actual yielded prefix**. Their capacity corollaries are at lines 79 and 131. These are input-only whole-query bounds. They do not require completed execution, future request counts, or a future capacity oracle.

The recurrence is already proved: `NativeBudgetNumbers.lean:13–18` defines `N(0)=1`, `N(h+1)=1+R²*(1+A*N(h))`, and `E(h)=1+A*N(h)`. `NativeBudgetCompile.lean:24–41` fixes the original uniform profile and computes costs from original heights. Warm hits can return arbitrary physically admitted values without invalidating this single-query budget: the current query returns those values but does not start new queries on them.

The remaining root premise is the **cumulative** numeric plan. `OuterNumericEntries.lean:30–32` requires `ParentCapacity` at every reached parent body. `OuterAdmission.ranges` at lines 136–143 already derives the old range plan from initial admission and this numeric plan. Reach admission is therefore complete; the next task is to derive the numeric plan from initial resources.

All shortened module names below refer to `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinary*.lean`, unless a full name is given.

## Smallest next producer theorem

Add a returned-profile component, for example `NativeOutputProfile.lean`. Reuse `NativeProfile.NodeShape`, `RowsShape`, `EdgeShape`, and `ChildrenShape` at lines 19–36. These predicates constrain every ordinary descendant. Reuse `NodeShape.mono` and the other monotonicity laws at lines 64–93, membership laws at lines 97–146, and `pairs_length_le` at line 232.

Use the following conditional certificates, quantified over profiles rather than one ambient profile:

```text
NodeCertificate request result :=
  request.domain.key.seen = [] ->
  forall R A,
    NodeShape R A request.left -> NodeShape R A request.right ->
    NodeShape (R*R) (max A 1) result

EdgeCertificate request result :=
  request.domain.key.seen = [] ->
  forall R A,
    EdgeShape R A request.left -> EdgeShape R A request.right ->
    EdgeShape (R*R) (max A 1) result

Stored native :=
  Returned NodeCertificate native.nodes /
  Returned EdgeCertificate native.edges
```

An initial implementation can require `request.domain = emptyDomain` instead of empty `seen`. Match the chosen condition in every producer and hit theorem. Do not claim this for arbitrary seen domains: the repeated-pair branch can return a reference even when both operands are ordinary.

The `max A 1` is necessary for a common node/edge certificate. `SourceEqualityNativeCheckedCode.lean:29–30` constructs a rejected edge with children `[Empty]`. Thus a standalone edge output need not have arity at most `A` when `A=0`. A sharper **node** arity bound `A` is a separate possible theorem: `InternedConstructorTemplates.surviving` at lines 234–235 removes rows with an Empty child before `makeNode` at lines 248–253. Do not use that sharper claim for an edge returned before this filter.

First prove only the structural lifecycle: empty native tables, advance, lookup, demand, and finish at the exact evaluating owner. `Stored.lean:98–137` supplies the existing pattern. Safe warm-hit owner equality is already available from `SourceCurrentAllocatedNativePhysicalCache.node_request_exact` at line 173 and `edge_request_exact` at line 189. The new warm-hit theorem must read the certificate for that exact stored owner and return it for the same literal result. Finishing may consume a locally proved producer certificate, but that lifecycle theorem alone is not the final producer theorem.

Then prove a producer theorem on the **same actual checked trace**:

```text
node_trace actualTrace initialGood initialSemantic initialOutputStored originalProfiles
  : OutputStored after.native /\ NodeShape (R*R) (max A 1) actualResult
```

Provide the edge analogue. Residency, existing structural `Stored`, and height bounds can remain separate conclusions or be combined with the frozen `Execution.node_trace/edge_trace` at lines 246–269. No supplied result shape, successful recursive callback, or final-state invariant belongs in the public producer premise.

## Why the existing warm interfaces need a bridge

* Current `Stored.lean:24–38` retains ordinary domain and both input-relative height bounds. It has no row or arity bound.
* `SourceCurrentAllocatedNativePhysicalCache.lean:20–37` retains input readiness, returned residency, checked keys, and machine validity. Its header explicitly excludes completed body execution. `SourceCurrentAllocatedNativePhysicalCompletion.Good` at lines 27–31 uses this physical invariant.
* Current `SourceEqualityNativeDemandProvenance.NodeProduced` at lines 42–50 and `EdgeProduced` at lines 53–61 record an actual checked body completion. Their historical initial premise is only `NodeReady` or `EdgeReady`; it does not include a profile certificate for warm cells used by that body. The recorded language law also does not bound redundant rows.
* Historical `SourceRecursiveIntersectionThunks.Valid` at lines 67–71 is different. It stores eager-kernel `Produced`. `SourceRecursiveIntersectionMemo.Produced` at lines 98–102 includes valid source-machine inputs and an actual eager execution; `SourceRecursiveIntersectionEdgeMemo.Produced` at lines 77–81 does the same for edges. A new eager producer-profile theorem could derive warm profiles **if** an explicit current checked-to-that-source-provenance adapter is also proved. These older definitions do not supply that adapter.

The new returned-profile component is the smallest direct route for the current checked engine. It is not a claim that additional stored data is logically unavoidable. A proved causal-history or source-provenance bridge could derive the same invariant. Preserve the distinction between these two routes.

## Noncircular producer proof order

1. Prove profile laws for actual `makeEdge` and `makeNode` results, including coherent cache hits. `InternedConstructorTemplates.lean:228–253` fixes literal children, filtering, and canonical rows. Neither filtering nor canonicalization increases row count.
2. Prove local checked code certificates. Ordinary node rows enumerate `pairs`; their count is at most `R²`. Accepted edge children enumerate the literal zip and inherit recursive node profiles. Rejection uses the one-child sentinel and skips child requests. Empty and self branches preserve or weaken the input profile. Domain/profile inversion excludes Mu, reference, and union branches.
3. Interpret actual traces while threading `OutputStored`. At a warm hit use the existing returned certificate. At a miss use the structurally smaller trace certificates, derive the exact local result profile, and install it only at that owner's finish. `Code.lean:32–98`, `Node.lean:77`, `Edge.lean:158–176`, and `Execution.lean:77` are the current compositional patterns. Add new modules; do not substitute the old eager interpreter.
4. Derive cold and serial-query corollaries. A meaningful kernel runs one actual completed query, then a warm repeat and a new query using its result. The second input profile must come from the first producer, with no second result-law or output-profile premise.

## From output profiles to a root reservation

| Stage | Existing exact endpoint | Next bound needed |
| --- | --- | --- |
| Projection | `Projection.forest:165`, `Target.operand:112` | Output profile and constructor requests for the literal selected path and captured forest. Union of selected rows can increase row count. Account for actual source occurrences and path depth; do not infer this from height alone. |
| Required children | `Required.node:264`, `children:271`, `rows:278`, `requireAll_done:286` | Strengthen positional `NodeNarrow`/`EdgeNarrow` to row/arity profiles and count actual rebuild Work. These relations currently assert only domain and height (`Required.lean:28–33`). Row deletion and empty replacement must follow the actual graph. |
| Merge | `Merge.allocated:103`, `finite:116`, `merge:128` | Bound actual grouping, recursive columns, Top-row construction, and final node requests. Extend or derive the completed winner's output profile. `MergeCache.Stored:20–21` currently asserts only domain; first-installed winner readback at lines 48–70 must retain the bound for the winner, not a losing candidate. |
| Target and shared leaf | `Target.fold:129`, `target:148`; `Shared.leaf:152` | Follow projection+merge head, recursive tail, then native intersection, with the literal first-seed rotation. Compute the next query budget from the derived intermediate profiles. Preserve warm native/merge tables; class-local target-slot hits reuse their captured profile. |
| Edit and class pass | `Class.verified:36`; `ClassPass.fold:64`, `pass:84` | Count actual row/child visits from the finite signed edit trie and input profile. The right fold captures the returned tail forest, so update the envelope between classes. Bound record count, paths per record, and trie size from actual precheck records. |
| Local, parent, outer | `LocalCapacity:33`; `ParentCapacity:33`; `OuterNumericRoot.finite:36` | Combine all earlier constructor costs and returned profiles into a decreasing remaining supply. Propagate the bound through actual earlier prefixes to every raw reached parent. Use existing `OuterAdmission.ranges`; do not assume the numeric plan that this accounting must prove. |

The first cumulative endpoint should be a target/fold theorem with explicit initial row/arity/height profiles, path-list size, and a computed constructor reservation. It should derive both `TargetCapacity` and an output envelope from those initial data. `TargetCapacity.lean:33–41` and `SharedCapacity.lean:35–45` show the exact earlier-prefix points where capacity is currently required. After that, lift the same accounting through edit, class, pass, local, and parent stages. A direct whole-root formula before these producer bounds would conceal the missing intermediate resource facts.

## Complexity and remaining boundaries

The proved native recurrence counts the full expansion, including repeated occurrences. It does not rely on memo savings and does not establish a polynomial bound. Serial intersections can repeatedly square a row envelope. Whole reduction also depends on finite path/record/trie sizes, projection and merge fanout, and repeated generated outer operands. Height alone cannot bound these quantities.

The current native budget counts node/edge constructor Work and the associated two supplies. It does not bound equality-interner allocation, thunk handles, global memo counters, host allocation, or execution time. State those resources separately if a later machine theorem needs them. General Mu/reference/union execution, repeated outer fixpoints outside this finite domain, concrete noConstraint CAF evaluation, GHC demand/publication, and solver/IO transfer remain separate library/runtime obligations. Preserve all earlier proofs and the rule that every Haskell repair must first be recorded in root `FINDINGS.md`.
