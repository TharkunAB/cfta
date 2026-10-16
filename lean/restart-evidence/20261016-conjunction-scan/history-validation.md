# Covered-history entry for current conjunction Scan

Date: 2026-10-16 07:04 CEST.

Source: `lean/MicroCFTA/SourceCurrentConjunctionClassHistoryEntry.lean`.
The 102-line source is frozen at SHA256
`5281ba7124f3c12c5919d4329b217a15b8612db61ebe4a7a291950e865d92a12`.
No older source file was edited for this task.

## Validation

- Pinned Lean 4.34.1 Lake focused build: terminal 0, 1276 jobs.
- Raw build log: `history-build.log`.
- Only the existing unused `inputs` warning appeared in an older dependency.
- Standalone final probes: terminal 0, no warnings.
- Three public axiom probes and three signature checks passed.
- Each probe uses only `propext`, `Classical.choice`, and `Quot.sound`.
- Seven kernel examples passed. They check literal-state readiness,
  availability, closedness, Original syntax, final interner identity,
  empty-fourth-memo correctness, and actual empty-expression construction.
- The initial standalone log retains a repaired probe-only reduction error.
  Proof source did not change after its successful first build.

## Entry and completion

`constructed width history valid expression covered value heap built`
derives current `Scan.Ready` at the literal checked state
`⟨initial width ⟨heap, Cache.emptyState⟩, MemoAllocation.initial finalCache⟩`.
It also returns Available heap value, value.free = [], and Original value.
OriginalHistory.constructed derives Good and SemanticReady. The same covered
history passed to ClassHistoryEntry.constructed derives CostHeap. Empty
native tables derive Scoped and Idle directly.

`finite` constructs the actual new conjunction Scan from that state.
It returns final Ready, physical Effects, retained forest availability,
fourth-memo Correct, and fourth-memo Extends. It has no supplied initial
Good, Ready, semantic heap, cost heap, loaded fields, scoped cache, Idle,
or historical completed Scan premise.

`cold_finite` starts the fourth memo empty and derives its initial Correct
invariant. It retains the actual final interner from the causal history.
Both native tables, the domain table, and completed equality-operation
memo tables start empty. This is the explicit cold model projection.
It does not prove a runtime table reset or source initialization schedule.

## Remaining explicit premises

The endpoint takes one actual covered allocation History, validity of its
initial interner, and actual successful original construction. The selected
forest is available in the constructed heap. Every selected original path
is proper. Actual reached machine-word ranges remain explicit. The generic
`finite` endpoint also takes initial fourth-memo Correct; `cold_finite`
derives it for the empty memo.

The actual current conjunction Scan is finite under those premises.
Exclusion of every class-satisfying original witness still needs the exact
seeded-query semantic admission and warm-cache transport component described
in `seeded-findings.md`. No new exact-language claim is made here.
