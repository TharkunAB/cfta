# Expand the exact native request and initial machine projections

Timestamp: 2026-11-14T20:36:36.680188+01:00
Status: UNCOMPILED. Root owns strict validation and publication.
The clear-writing skill was applied to this note.

This revision changes only the final actualKernel transport. It explicitly
expands the local request, local before and SourceRecursiveIntersectionThunks.initial
before reducing the zero extra fuel. The failed proof retained opaque
request.domain, request.left, request.right and before.machine projections.
The expanded expressions are the same literal emptyDomain, physical left/right
operands and initial machine. No operation, theorem header, source-field
condition, actual completion, Bounds, endpoint or premise changes. All other
proof bytes remain unchanged. The older frozen packet remains unchanged.

The raw public header is byte-identical. This remains an EXPLICIT COLD native
request over actual source component slots. Root-worker reachability and the
distinct allocated checked Trace remain outside the claim. All operand
Available, closed, Origin(encodedLibrary lib) and original-U facts still come
from the actual component calls and original source provenance. No stronger
Type role or SemanticHeap fact is inferred from atoms.

Previous whole-module strict checking failed only at this final transport.
This revision still requires strict elaboration and axiom checks. No proof
credit is claimed before acceptance. No compiler, live edit, Git write, board
action, child agent, Haskell change or FINDINGS edit was made.

Source SHA256: 9ad515ab80b77dc7f28222f6c5c40d621ee108ebae073ca038c40e160a139731
Previous source SHA256: 61e18958421bccb37edea612bd4ba4e7c1b16ce8ccb572a126fed3d095c94c4b
Public probe: current_component_fields_cold_native_result_atoms.
Namespace: MicroCFTA.SourceSynthesisCurrentComponentFieldNativeAtoms.

Exact proof diff:

```diff
--- previous/SourceSynthesisCurrentComponentFieldNativeAtoms.lean
+++ repaired/SourceSynthesisCurrentComponentFieldNativeAtoms.lean
@@ -117,7 +117,7 @@
       leftFacts.1 rightFacts.1 leftFacts.2.1 rightFacts.2.1 leftAtoms rightAtoms
   have actualKernel : execute top SourceEqualityPCSNativeEdge.conjoin bound IntersectionEmptyDomain.emptyDomain
       left right machine = .done value after.machine := by
-    simpa only [Nat.add_zero] using exactKernel 0
+    simpa only [request, before, SourceRecursiveIntersectionThunks.initial, Nat.add_zero] using exactKernel 0
   have returned := closed.result value after.machine actualKernel
   exact ⟨⟨leftFacts.1, leftFacts.2.1, leftFacts.2.2, leftAtoms⟩,
     ⟨rightFacts.1, rightFacts.2.1, rightFacts.2.2, rightAtoms⟩,
```
