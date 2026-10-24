# Existing checked-Demand returned-value route

Review cut: 2026-10-24T18:00:53+02:00. Verdict: the proposed availability/closedness/model-handle bridge is already derivable on the existing physical checked-request domain. A new scope framework or recursive result induction would duplicate installed results. This is a bounded source inventory and composition review. No theorem, action, instance, script, or compiler job was authored or run.

The sealed prospective OrdinaryBranches next assessment recommends a new checked-return postcondition. Its negative claim misses `SourceCurrentAllocatedNativeActualScope.step` and `SourceCurrentNativeOpenRequestResults.node_result`. Preserve that assessment as history and correct the recommendation separately. The distinction it makes between the older executor and checked Demand is valid, but it does not establish this gap.

1. **The actual checked request is already named.** `SourceCurrentAllocatedTargetQuery.lean:32–37` defines `Step left right before value after` by a `SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace` of `requestNode emptyDomain left right`, from `before` to `.code (.pure value)` at the SAME `after`. The local `Checked` notation is literally `SourceEqualityNativeDemand.State` (line25). Its `Step.done` gives actual finite `SourceEqualityNativeDemand.execute`; `Step.unique` identifies both returned value and entire state. This is neither the older executor nor an arbitrary intersector law. A physical Trace also retains each reached instruction's `PhysicalExecution.Inputs`; a bare successful executor equation alone must not be silently promoted to this stronger object.

2. **Availability already follows at that return, including warm hits and cold finishes.** Exact public header from `SourceCurrentNativeOpenRequestResults.lean:69–75`:

```lean
theorem node_result [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (request : NodeRequest Symbol Guard) (before after : Checked width) (value : Value Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after) :
    Available after.native.machine.heap value := by
  cases requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none =>
```

`Good before` supplies `good.native` for this premise. No original/closed operand premise or `NodeProduced` premise is needed for this availability result. Its keyed proof inspects the actual returned cell or checked finish; the unkeyed successful path is Empty. The physical `Inputs` finish check contains current Available, not a semantic completed-body oracle. `SourceCurrentAllocatedNativeRequestResults.finish_node_result:25–28` and `.edge_result:104–108` are the related finish/row results.

3. **Closedness, scoped memo cells and idle state already follow for the SAME actual result.** Exact `SourceCurrentAllocatedNativeActualScope.lean:54–66`:

```lean
theorem step {left right result : Value Symbol Guard} {before after : Checked width}
    (actual : SourceCurrentAllocatedTargetQuery.Step left right before result after)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped before.native)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    SourceCurrentAllocatedNativeScopeCache.Scoped after.native ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ result.free = [] := by
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left before.native.machine.heap
    good.native.machine.1.coherent leftAvailable leftClosed
```

The installed proof derives Original from the coherent available closed operands. `word_ranges:32–50` derives the request's reached WordRanges from its physical Trace. `ScopeCompletion.initial_complete:650–674` constructs a scope receipt for the same checked executor. `actual.unique` then equates that receipt's value and complete state with the supplied actual return (ActualScope83). There is no independent desired-result scope premise here. `ScopeCache.NodeLaw:21–22` means `ResultScope.Scope request.domain.key.seen result`; `Scoped:29–31` applies this to returned native node and edge cells. `ScopeCompletion.request_complete:610–627` also supplies nonempty-domain result scope under its explicit source scope/completion/resource premises. `ColdClosedExact.cold_complete:37–77` already combines checked contextual language with result closedness and scoped cells.

4. **Keeps and full checked effects also already follow.** The smaller `SourceCurrentAllocatedNativeSemanticTraceReadback.lean:137–142` header is:

```lean
theorem effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {control rest : Control A} {before after : Checked width}
    (trace : Trace fuel control before rest after) (valid : Good before) (fields : Fields control before) :
    Good after ∧ Extension before.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧ Fields rest after
```

For this pure-return node request, initial `FieldClosure.Fields` reduces through `CodeFields.Fields` (22–32) to the pure continuation check, so it adds no output certificate. This supplies Good after, whole-machine Extension, constructor Keeps, and operation-cache growth. The larger `NativeTraceEffects.effects:30–37` additionally derives cost/semantic Effects with an initial CostHeap premise. `TargetQuery.Step.verified:102–121` returns a full receipt with availability, closedness, readiness, language and global-table facts when its explicit inventory admission, ranges and memos premises are available. Do not add those stronger premises just to derive a model handle. No named `TargetQuery.Step.keeps`, `.effects` or `.resultAvailable` declaration was found; use the existing trace theorem or receipt fields.

5. **Raw-slot prerequisites and computed result handle already have reusable producers.** `EnumerationObservation.PendingRealized:19–25` yields complete Available closed operands from the actual stored handle. `observed_realized:57–81` obtains this from the literal `getUnexpandedNode` success with genuine Total and a full compression Frame. After the checked request, Keeps transports old lookup/realization (`EnumerationNodes.lookupNode_keeps:50–76`; `EnumerationObservation.realized_preserved:45–54`). Final Good supplies coherent final constructor records. `EnumerationNodes.available_readback:35–38` then derives `∃ node, encodeNode result = some node ∧ lookupNode finalHeap node = some result`; no returned-handle certificate is an input. `Writes.allocate_available_realized:17–27` and `.write_available_realized:42–54` already install that computed handle at an actual fresh/allocated raw slot and preserve PendingRealized. Their alignment/slot-bound premises remain explicit. The model encoding is Empty=0, canonical node identity+1; it is not native NodeId extraction.

6. **The success-to-physical-trace bridge also exists, with an important boundary.** `SourceCurrentAllocatedTargetWorkerNative.of_done:26–35` accepts literal checked Demand `execute ... = .done value after`, Good/Idle before, two Available closed operands and explicit reached WordRanges, and derives the SAME `TargetQuery.Step`. `.of_done_ready:51–62` packages the current Ready fields; `.step_iff_done:66–82` states the exact equivalence on that domain. It does not derive WordRanges from an arbitrary raw success. For an existing Step, ActualScope.word_ranges already derives them. Thus no new result theorem is needed, but a caller that supplies only bare success must discharge the existing physical/range premises.

7. **Scoped input origins are also present, and do not imply generated-result origin.** `SourceCurrentNativeRequestSourceScope.node_prefix:30–47` derives actual reached queried NodeScope and incoming-domain inventory membership from Good/SemanticReady, closed available initial operands, node/edge bounds and room. `SourceCurrentNativeOriginalRequestScope.optional:80–111` additionally uses the SAME original build and actual optional prefix to obtain rooted original writers for queried inputs/domain names. It explicitly separates generated returns from those original inputs. These are not missing generic scope producers; they do retain real resource/source-history premises.

The older `SourceRecursiveIntersectionNativeApi.native_node_correct` and `SourceEqualityNativeScoped.Step.verified/complete` use `SourceRecursiveIntersectionNative.execute` with generic emptyGuard/conjoin and `SourceRecursiveIntersectionThunks.State`. They cannot replace checked Demand's operation-cache/error behavior. The route above uses checked Demand directly. `DemandProvenance.NodeProduced.spec` alone is not the noncircular route: its receipt definition already includes Available; the installed actual physical request results avoid assuming it.

**Remaining composition boundary:** bind the intended enumeration terminal callback to this actual checked Step/native return, derive both operands from its actual raw-slot reads, then compose the existing computed-handle writes with the correct reject/write/eliminate/ancestry/waiting order. A full compression Frame does not hold across changed values. Source-specific `checkEmpty && reachesConstrainedMu && provablyEmpty`, native cached-index maintenance, native NodeId extraction, finite resource admission and the shared-driver/terminal caller connection remain separate. None of these boundaries justify reproving the already-established checked result closedness. H6 remains the existing strongest combined finite-calls result; no new end-to-end or convergence claim follows from this inventory.

Next checkpoint must retain the immediate previous **39 custody inputs, not 26**. No generic adapter work is requested by this inventory.

Read scope: exact public headers/definitions and relevant installed proof cuts above; full ActualScope, OpenRequestResults, RequestResults, TargetQuery, TargetWorkerNative, Nodes/Observation/Writes, RequestSourceScope and OriginalRequestScope were read. Other modules were inspected at the cited cuts. Search results are not a claim to have manually read every SourceCurrent module. Whole-file identities below pin the inspected sources; they do not widen that manual scope.

| Source under `lean/MicroCFTA/` | Header/definition cuts used | Bytes | SHA256 |
|---|---|---:|---|
| `SourceCurrentAllocatedTargetQuery.lean` | 19–37,40–55,57–121 | 8024 | `20231be214e9d62e97f92b41d32fce62be959e78e24141c9a7fe73dd2060e9a6` |
| `SourceCurrentAllocatedNativeActualScope.lean` | 14–18,32–50,54–85 | 4387 | `924446496dd6d5fe0032bd703411d0dbdb5d5595e904d56516a2cb422e18f6da` |
| `SourceCurrentNativeOpenRequestResults.lean` | 14–20,69–80 | 5024 | `c6867dcc4d58b33cbf27a6df96b08401e969e2e5a27da326fe7a635d3baecd51` |
| `SourceCurrentAllocatedNativeRequestResults.lean` | 14–20,25–48,58–135 | 8661 | `80244db37455f61eacc4e9e30b7b4f1f90a5a0b03f8cc05a23bbedc162eb94d3` |
| `SourceCurrentAllocatedNativeSemanticTraceReadback.lean` | 137–155 | 19537 | `ee32a30dc63699b7d4c6a4937d3a827828d871c50154bee22023da53b4636dc9` |
| `SourceCurrentAllocatedNativePhysicalCompletion.lean` | 27–32 | 25356 | `ad0fa0abaa240d8bf981734abd0ab6ae66d500c439a76084f1cc5c16ade581d2` |
| `SourceCurrentAllocatedNativePhysicalTraceCompletion.lean` | 30–39,90–110 | 44726 | `eb9dcb6701c7742118b227da9d6322a6e9170eb6fa989c3db6369a99b2064008` |
| `SourceCurrentAllocatedNativeCodeFields.lean` | 22–32 | 12990 | `6bcd4a98e74f63f416410d4d08c44073ba9d9afb0562ecdafbfba8437083f886` |
| `SourceCurrentAllocatedTargetWorkerNative.lean` | 26–82 | 4880 | `1bcd61ce26ff5f8f33f636b3ec18e1cf8d063babbc3cd76d52cba863619dd619` |
| `SourceCurrentAllocatedNativeScopeCompletion.lean` | 38–55,578–699 | 57878 | `d3ee51746d0affdfb623db252c6277409bf0167a0848679425281d59f5d6d2e8` |
| `SourceCurrentAllocatedNativeScopeCache.lean` | 21–31 | 13094 | `8feccd12a39470a81738e635283e6dd9b31f716590db40894f6f5db089c78a00` |
| `SourceCurrentAllocatedNativeColdClosedExact.lean` | 25–77 | 5519 | `c61f3d8d8f595ac38d3cfdb80eb2be23b5f06e74b56112379184017dc2ce803b` |
| `SourceCurrentNativeRequestSourceScope.lean` | 30–64,67–117 | 10087 | `25db65fa96d236d93426e83eb757d112fff57d6c64c134474027e0dcd344d8be` |
| `SourceCurrentNativeOriginalRequestScope.lean` | 31–43,80–111 | 7594 | `cd8d2d2f79aa3edbdbcb7905cab0f900d50f43d81c05407811c9fc63ac501d96` |
| `SourcePruningEnumerationNodes.lean` | 35–38,50–76 | 3546 | `1fb4077739402c31ec48d4bfa8254ef9c1b7453601290dfcd1c0c0031eeee8a4` |
| `SourcePruningEnumerationObservation.lean` | 19–25,45–54,57–81 | 7357 | `5a7b858adc4febb75621b9836053f308924c22d5fd7662741da61cbdab629bf4` |
| `SourcePruningEnumerationWrites.lean` | 17–27,42–54 | 4216 | `32864f9158615ee7787c7490356471489978a5622ea984d904f7b03329510a7e` |
| `SourceEqualityNativeScoped.lean` | 40–93 | 8669 | `572d68d46d10fa921bd49b084d69882d746f617e54c3f443907ce8a989292997` |
| `SourceRecursiveIntersectionNativeApi.lean` | 16–39 | 8719 | `6e090c3d5d38f1485c238cdf87790bd457a8f7cfc2f760af6c8f6c9d76732348` |
| `SourceRecursiveIntersectionNativeResultScope.lean` | 21–75 | 5722 | `d91166066815a749b56deae529d131666ee3c13d1109ad04c7e0c8ffb1914537` |

Historical prospective assessment inspected: `/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024-next-assessment.md`, 26047 bytes, SHA256 `ac74a3379281e3b270d286fda6e8c8ed7d8859de1853c7d72ab1401ebec5f94f`. It remains unchanged.
