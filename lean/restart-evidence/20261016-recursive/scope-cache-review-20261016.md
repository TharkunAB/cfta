# Independent scope and closed-root review

Reviewed at 2026-10-16 06:13 CEST. The source owners confirmed the reviewed modules are frozen. This task used source reads only. It ran no build and changed no proof source.

No material defect, hidden parent-scope premise, or supplied recursive completion callback was found.

`ScopedMuCertificates.optional_scope` consumes the actual optional-binder return. It derives removal of the new pair from the child's free-name scope. `mu_certified` derives the entered domain key and uses `extend_seen` to place all possible child names in the new pair plus the original seen list. The continuation receives only the exact entered child's scope and current availability and `SemanticReady`. It does not assume initial semantic readiness, an input model, a source history, or parent scope. Its primitive `done` observation is local to the optional-binder continuation, not an assumed completed recursive query.

`ScopedNodeCertificates.node_certified` rewrites the actual dispatcher decision. Mu, union, row, repeated, reset, swap, self, and reference branches use their corresponding local certificates. Reference reads preserve the incoming domain. Failure certificates are conditional and do not establish completion.

`ScopeCompletion` discharges its private child-body obligations by strong induction on independent original-input request bounds. It derives current physical checks, fields, semantic heap readiness, and cache scopes through the actual checked interpreter. A miss derives local result scope before finishing its exact evaluating cell. A warm hit uses both physical validity and the separate initial `Scoped` invariant. Rejected checked prefixes select the sentinel and skip child demand. The cold endpoint derives initial cache scope from empty tables and returns cached free-list closedness from the empty-domain result scope.

`ColdClosedExact.completed_unique` derives equality of returned values and the complete checked states. It extends two successful executions to the same summed fuel through `done_stable`. `cold_complete` invokes the independent contextual and scope endpoints from identical actual initial state, control, and operation cache. It transfers final scoped caches and `value.free = []` onto the contextual receipt. The resulting exact intersection law and cached closedness therefore concern the same actual value and complete final state. No output equality or extra future-state property is assumed.

Initial `Good`, `SemanticReady`, available closed `Original` operands, and actual-prefix `WordRanges` remain explicit. `Good` includes same-cache field availability and operation validity; it contains no parent result law. General scoped entry also retains independent `Completes`, growth/history, and `ActiveAbove` obligations. Warm history admission is separate. The displayed combined endpoint does not itself conclude `CostHeap`. Runtime/GHC publication, concrete identity and machine capacity, and whole Haskell caller correspondence remain separate adapters. No old eager execution or `NativeResultScope` meaning transfer supplies the new scope proof.

Owner-reported validation: Mu certificates GREEN1091, node certificates GREEN1093, ScopeCompletion GREEN1099 with 8 public axiom reports, 8 signatures, and 3 kernel examples; combined endpoint GREEN1123. These reports are separate from this source review. No validation command was rerun here.

Frozen source SHA256 values:

```
bc21083355ec62a3f449a9ed0a471cf0a7773d087fd07644ff352b32065d49a2  SourceCurrentAllocatedNativeScopedMuCertificates.lean
3e829486a816f696690083c5aa8ac5919b7f629fcc0d77f963603179a28aec00  SourceCurrentAllocatedNativeScopedNodeCertificates.lean
d3ee51746d0affdfb623db252c6277409bf0167a0848679425281d59f5d6d2e8  SourceCurrentAllocatedNativeScopeCompletion.lean
c61f3d8d8f595ac38d3cfdb80eb2be23b5f06e74b56112379184017dc2ce803b  SourceCurrentAllocatedNativeColdClosedExact.lean
4e5787a250635f6256c14ed257b70551592591e65f102fae3572582d92a54d86  SourceCurrentAllocatedNativeScopedCode.lean
109fbbcd69caf68c4247b92b8727b54009771b88d466d4c3e14f5310d55deb91  SourceCurrentAllocatedNativeScopedCertificates.lean
```
