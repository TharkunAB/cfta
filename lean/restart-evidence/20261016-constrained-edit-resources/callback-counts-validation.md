# Exact shared edit callback counts

Validated 2026-10-16 21:27 CEST.

Frozen source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts.lean`.
SHA256: `ae311a6e85edc82c6cce1949fb533d1ee91f1f2e9e0f1dad99314e82c43fd70f`.

## Contract and scope

NodeCount, ChildrenCount, RowsCount, and ListCount are proof-indexed propositions on the literal current SharedEditGraph. They retain the exact graph proof, input and result records, and complete before/after shared states. Node leaves count one call to SharedTargetLeaf. Empty below-edits and ignored list-root leaves count zero. Ordinary nodes use their row counts. Selected children and rows add their exact earlier and later counts. Recursive exposure copies the body's count.

The four count-existence theorems consume only a supplied finite actual graph. They do not prove that an execution completes. The bound methods consume a count certificate and the original finite ordinary domain. They use ValuePositions, which includes Empty and repeated positions. The recursive exposure case is impossible under that domain. NodeCount.profile and ListCount.profile compose the existing initial profile, height, and forest-length bounds. No callback law, capacity, range, semantic model, desired output profile, or future invariant is a premise.

Each counted shared Leaf contains one native query after Force. Internal Target queries on a first Force are separate resource events. This count does not omit or duplicate those events; it does not claim to count them. No equality, guard, identity-distinctness, or canonical-input restriction is added to the finite ordinary domain.

## Checks

- Final direct attempt 9: exit 0, no diagnostics, with unused-section-variable and unused-variable linters enabled.
- Root-owned canonical Count/Class batch: exit 0, 1381 jobs, `edit-count-class-build-1.log`. The log has only the historical `InternedFreshOrdinaryClosedCompletion.inputs` warning.
- Imported public probe: exit 0, `callback-counts-public-1.log`. It checks 14 public relation/theorem signatures and 11 constructors. All 25 declarations have axiom reports.
- Imported integration probe: exit 0, `callback-counts-kernels-4.log`. All 4 kernel signatures and axiom reports pass.
- Final direct, public, and kernel logs have no errors, warnings, or `sorryAx`. Public and kernel axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

The kernels establish four distinct source cases:

1. A below-edit on Empty and a list-root leaf both count zero at unchanged literal states.
2. A supplied actual shared Leaf on Empty counts one and fits the zero-height, zero-row envelope. No law about its result is assumed.
3. Two actual sequential Leaf calls on repeated Empty positions use the same callback token. The constructed ordered EditList counts two and fits the new forest bound.
4. Two copies of the same original row count two calls. The second call starts at the exact state after the first row's literal makeEdge and advanceHeap. Both raw row constructors and the final shared state are retained in the constructed EditRows.

The last three kernels verify supplied concrete finite component graphs. Their component graph premises are not universal callback contracts or a claim that those components always succeed. No kernel assumes a count or desired result law.

Failed direct attempts 1-8 and their exact source copies are retained. The failures concern implicit index/proof inference and automatic mutual recursion. The final proofs use explicit mutual recursors. Kernel attempts 1-3 and their source copies are retained. The final kernel removes an unused let binder and makes arithmetic/count arguments explicit. The recursor signature scratch source and log are also retained.

No production source changed after direct attempt 9 and the canonical build. No older source, Audit, Haskell, restart authority, Git state, or old evidence changed. Whole edit/class/pass/outer cumulative reservation production remains a separate task.
