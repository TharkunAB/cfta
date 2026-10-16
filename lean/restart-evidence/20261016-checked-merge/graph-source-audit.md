# Source allocation and predicate audit

Reviewed 2026-10-16 08:42 CEST against the current working tree. No Haskell bug is asserted.

## Large groups and equality allocation

`Interned/Operations.hs:613` applies the typed merge memo before the body. A closed ordinary body groups by literal symbol and child count (:615-630). Groups larger than four construct direct `Edge` with column results (:622-624). `Interned/Type.hs:537` expands this constructor to `internEdge (UninternedEdge symbol children noConstraint)`. Its constraint field is strict (:499-502). `Constraint.hs:204-205` defines `noConstraint = Constraint EmptyConstraints Top`, with both Constraint fields strict (:116-120). `Equality/Constraint.hs:313-314` expands EmptyConstraints to EqConstraints []; that constructor calls the canonical equality interner (:270-286).

Thus a demanded large-group edge demands the canonical empty equality value, possibly making its first allocation. There is no separate guard interner for the Top tag. Repeated demands can use the existing canonical empty key. The direct Edge path does not execute mkEdge's contradictory/fitsArity guard and does not call the full equality accessor or the combine/descend memo operations.

The equality sidecar must retain this constructor effect even if final mkNode removes the edge because one merged child is EmptyNode (Type.hs:546-552,581-585). An empty original edge list does not itself construct a Top row. A large nullary group still constructs its Top row even though there are no column calls.

## Other branches and memo boundaries

Small groups use setChildren and recurse through their original children (Operations.hs:624). Mapping preserves arity, so setChildren uses direct internEdge with the original constraint (Type.hs:398-400); its mkEdge branch is not reached. Such a group does not introduce its own new Top constraint. Recursive child calls can reach large groups and introduce Top there.

A root Mu, union, reference, EmptyNode, or open ordinary input returns unchanged from the merge body (Operations.hs:631). Memo hashing uses the tagged physical identity (Type.hs:321-330). A completed resident hit skips the body. Runtime memo entries are lazy: memoWith passes `f x` unevaluated (Memo.hs:93), and insertKeepingFirst does not force the saved value (Cache.hs:135-155). A hit that returns an unevaluated published thunk can still demand the original saved body. Completed-hit graph laws do not establish a general zero-effect runtime hit.

## Comparison predicate and demand order

Within large columns, retained closed Mu values bypass comparisons. Other closed children try the original recursive covers in order (Operations.hs:640-648). `subsumes` short-circuits EmptyNode, identity, and repeated pairs, then reads actual nodeEdges (:660-673). Only a matching symbol/arity candidate tests literal `edgeConstraint wide == noConstraint` (:672), before child comparisons. This predicate can itself force the noConstraint CAF before the final Top row. The current pure selection instruction does not record that equality-allocation event.

The old `SourceMemoGate.plain` predicate is not this literal comparison. The verified kernel example `Constraint (some []) (Guard.and [])` has plain=true but differs from literal Top. Literal Top itself matches both tests. A preliminary proposed reflexive-Same example was rejected: source Constraint.hs:173-174 intentionally leaves reflexive Same as a residual, and its plain predicate is false. The preserved counterexample uses empty And.

The graph retains the existing completed column-first schedule. Haskell forces the strict noConstraint field before entering the edge interner lookup (Cache.hs:171), but that does not force all column computations in the graph's order first. Exact GHC forcing, early publication, comparison CAF effects, and concurrent interleaving remain separate obligations. Group-bucket order also remains the existing logical source-group adapter, not a proof of native HashMap.elems enumeration.

## Reusable Lean receipts

- `SourceEqualityMkEdgeAllocation.emptyField` and `emptyField_correct` (:76-86): actual canonical empty-key interning, Valid/Grows, both operation tables unchanged.
- `SourceCurrentConjunctionFieldAllocation.empty_field` (:84-92): same-cache actual successful Top field load, with no supplied future field premise.
- `SourceEqualityConstraintFieldLookup.load_of_receipt` (:55) and `load_of_construct_grows` (:126): exact normalized readback and retained successful load.
- `SourceCurrentConjunctionEquality.FieldAvailable/Fields` (:24-29), `Fields.grows` (:64): the equality sidecar invariant needed by the new checked lift.
- `SourceCurrentMemoMergeGraph.large/group/body` (:67-89), `Call.hit_unchanged` (:183): old raw constructor/merge-memo erasure target.
- `SourceCurrentMemoMergeFieldHeap.call_heap/native_heap` (:150-169): generic annotation retention still takes Top annotation explicitly; it does not allocate the missing field. The new allocated physical proof must derive that annotation at each reached Top row.
- `SourceCurrentAllocatedMergeGraph.Run.graph/Call.graph/run_lift/call_lift`: actual old heap graph and constructive allocated lifting. Equality validity and completion belong to the separate Physical module.

No frozen file, Haskell file, Audit, documentation, or Git state was edited by this source audit.
