# Parent worker independent source review

Reviewed 2026-10-16 14:12 CEST. Verdict: no material defect found in the literal parent definition or its four public branch lemmas. This review does not establish whole-library correspondence.

## Exact scope and source

Reviewed `SourceCurrentAllocatedParentWorker.lean`, SHA256 cd54649ba473f2cf293bf359d7477e2d9059ed4777bd3c697fd702b285c129fa. The worker mirrors the completed serial parent phase at `cfta/src/Data/CFTA/Equality/Operations.hs:160–168` and the raw guard short circuit at `cfta/src/Data/CFTA/Interned/Type.hs:563–568`.

`edge:73–84` tests raw contradiction before field lookup, local reduction, or child construction. Rejection runs the literal `SourceCurrentAllocatedMkEdge.reject`. It retains the sentinel's constructor heap and actual canonical empty-field allocation. It requires no field lookup, available child list, inherited readiness, or positive lower-stage bound. Physical sentinel fields require initial Ready/At and follow `MkEdge.reject_correct`; the raw definition alone does not assume a coherent cache.

Live `load` is read-only at the initial `before.operations.constraints`. `.error message` and `.ok none` are distinct failures at the unchanged full Checked and both original memos. Missing representation is a model incompleteness outcome. It is not a source emptiness verdict or a cache-repair request. Loaded raw-guard equality and original-field admissibility remain explicit initial entry obligations in the semantic adapters.

`reduceChildren:65–70` invokes the literal Local worker once. Success uses its actual children, Checked, fourth memo, and merge memo. Failure retains its full local Fault. A failed class keeps the complete raw shared state and local target slots inside the nested class diagnostic. The parent does not reset, reconstruct, or discard that diagnostic.

`build:57–62` invokes the literal checked constructor once at that local return. Constructor failure preserves its own `actual.2`, including operations that the constructor may have allocated. It does not return the earlier local or original state. Success preserves the exact returned edge and full checked state; fourth and merge remain the actual local return. No premise or definition substitutes the old native scoped engine.

## Sentinels and later work

Raw rejection returns a Top-field sentinel with one Empty child, under the physical hypotheses of the constructor receipt. A live arity rejection can also select the same sentinel. The result need not retain the original child-list length or guard. The next outer descendant phase must use THIS returned edge's actual raw guard and children. Same-arity raw setChildren is a later phase and must not repeat MkEdge.

The wrapper itself has no outer result table, recursive descendant traversal, or busy-cell policy. These belong to the later eight-family worker. The source's mkEdge is lazy in its child argument on raw contradiction; this completed serial model preserves that short circuit without proving all GHC forcing observations. Host global tables, source lazy publication, machine keys, and equality-field initialization retain their separate adapters.

## Checks

The direct imported public probe prints axioms and full explicit signatures for `edge_rejected`, `edge_field_error`, `edge_missing_field`, and `build_error`. All four pass. Only propext, Classical.choice, and Quot.sound occur; a theorem may use no axioms. The signatures expose literal observations and no final readiness, semantic answer, or future completion law.

Seven imported kernel examples pass with no warnings:

1. A Bottom guard rejects at zero stage bounds without field or child facts. It retains native tables/domain, actual emptyField operations, fourth, and merge.
2. A live field error retains its message and original full state.
3. A live missing field remains distinct.
4. A failed class preserves its raw shared state and target slots inside the parent fault.
5. Local success followed by constructor failure retains the constructor's later state.
6. Local success followed by construction uses exactly the local returned children/state/memos.
7. Ready/At derives the actual Top sentinel, its one Empty child, residency, and independent empty edge language, with no input child list.

These examples test literal equations and integration. They do not supply a missing semantic body law. No canonical Lake, Haskell build, or source edit was performed for this review. The unchanged source reuses the validated 798 examples plus golden. `outer-worker-plan.md` records the next executable recursion and ownership interfaces and the independent termination boundary.
