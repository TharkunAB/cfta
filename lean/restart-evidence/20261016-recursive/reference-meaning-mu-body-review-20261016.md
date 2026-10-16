# Read-only Mu body review

Date: 2026-10-16 05:36 CEST.
Reviewed source: `lean/MicroCFTA/SourceCurrentAllocatedNativeMuBodyMeaning.lean`.
Reviewed SHA256: `dcb2b99fcd4913eaea206733c220bf4a9e38bf3d7a94e96381b9b489934c6c9c`.

No concrete proof-scope defect was found in the saved source. No build or dependency mutation was performed. This is a source review, not independent compilation evidence. The parent owns the pending focused build.

- The only semantic recursive premise is `childLaw` for the actual entered domain and the two unfolded original operands. No parent `NodeLaw` is assumed.
- `child.plan` derives actual physical checks from the completed local child trace. `through_heap` converts these to heap input checks. `execute_semantic` derives the middle `SemanticReady` from the initial one. Source domain entry leaves the heap unchanged, so the initial entered heap is definitionally the initial heap.
- The local child's `Keeps` premise already contains middle `Ready`. It does not contain the additional guarded and budget probe heap laws required by the Mu meaning theorem. The proof derives those laws through the actual trace.
- Child output availability derives actual optional-binder completion. The same observed completion supplies the source Mu law, the literal final optional-binder step, output availability, and final semantic heap preservation.
- The bound is exact for this composition: one enter step, `fuel` child steps, one optional-binder step, and one final pure return give `fuel + 3`. The resulting state retains the child's actual operation cache and native tables and advances only its heap with the actual optional-binder result.
- The latest theorem takes the actual selected branch disjunction `.bothMu`, `.leftMu`, or `.rightMu`. Each branch definitionally compiles to the same `compileMu` body. This derives the public `compileNode` execution conclusion. The selected branch adapter is now covered.
- Fixed original source facts, input model and ranks, original available operands, input scope, actual identities, initial domain cache validity, a recursive operand, and pair freshness remain explicit. So do the actual completed child trace and its physical checks, heap retention, available output, and local contextual law.

The theorem proves local body composition for the actual selected `compileNode` Mu branches. It does not derive the global recursive child trace or law, prove cache finish validity, or prove general current query completion. Explicit `started` and `finished` state definitions resolve state inference without changing the actual states or adding premises.

Other reviewed source hashes:

```text
ea90c7ca44ddfbe62fca1c6644726cd9cea84edac0fb56a4cb2506fe4a7bed0b  SourceCurrentAllocatedNativeMuSource.lean
3a93ddb3c82dc5874f64de1504cf032aa29a9e6a9ac9df4433cf4d3754368718  SourceCurrentAllocatedNativePhysicalTraceCompletion.lean
d79bfbe1a03ae121d0dde7d740080fbc9405f1448939bc0e41e4f3b5e53d39e6  SourceCurrentAllocatedNativeSemanticHeap.lean
```
