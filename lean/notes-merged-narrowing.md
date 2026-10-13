# Merged equality narrowing

Updated: 2026-10-13. Source refresh: `4d51f03` and `8ac24bb`.

## Source change

`reduceEClass` now calls `mergeAlternatives` on every peer projection before
the target intersection. The merge groups ordinary edges by symbol and arity.
It preserves the constraint of a singleton group. It drops the constraints of
a larger group and unions the children at each position.

This is an overapproximation. It can enlarge a language even at arity zero or
one, because it drops constraints. The complete equality reduction can still
preserve its language: the original edge constraints remain, and each edit
intersects the original node with the enlarged peer target.

## Repaired recursive call cycle

Let `A = mu x. {a(), f(x)}` and `B = mu y. {b(), f(y)}`. Both are closed and
productive. `union [A, B]` exposes four alternatives, including `f(A)` and
`f(B)`. Merging those two alternatives calls `mergedUnion [A, B]`. Both
recursive operands survive the filter. The old multi-operand branch then
calls `mergeAlternatives (union [A, B])` again.

The focused source probe timed out after three seconds before the repair.
The same failure occurs when the recursive children are retained
`InternedUnion` values. A guard that checks only `InternedMu` does not cover
that second case.

The local repair changes the multi-operand branch:

- If a retained operand satisfies `recursiveBoundary`, return `union others`.
- Otherwise, continue with `mergeAlternatives (union others)`.
- Keep the singleton branch unchanged.

The branch can expose a recursive union once. It does not recursively merge
that exposure. Thus it does not reproduce the same merge request. The result
can retain multiple alternatives below that boundary. The Haddock now states
this limit. Its edge-pairing bound applies at a merged ordinary root; it does
not claim a bound by the smaller input or a bound below recursive boundaries.

This repair does not prove termination of `subsumes`, recursive node exposure,
all merge executions, or repeated equality passes. Those are separate claims.

## Retained source probe

`lean/repro/MergedNarrowing.hs` contains the direct recursive case, the wrapped
union case, the constrained parent caller, and nullary guard widening. It does
not add a test to the production test suite.

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=microcfta lean/repro/MergedNarrowing.hs'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=microcfta lean/repro/MergedNarrowing.hs union'
```

Before the repair, both invocations stop at `merged root completed: Nothing`.
After the repair, all five checks return `Just True` in both invocations.
Each invocation compares membership of 27 unary terms, through eight `f`
constructors. It also checks the result of a parent `reduceEqConstraints`
call. The nullary example uses the distinct raw guards `Not Top` and
`Not (Or [Top])`; both are false, but their merged constraint is `Top`.

The core library build, both retained probe invocations, and Fourmolu checks
passed. The focused log is `/tmp/mcfta-merged-narrowing-repro.log`. All 620 existing Haskell examples pass after the repair. Both changed
production files pass Fourmolu; both active Cabal files pass Cabal-gild.
Log: `/tmp/mcfta-20261013-merge-repair-tests.log`.

## Checked Lean results

`MergedAlternativesSubsumption`:

- `Checked` records successful comparisons, including ancestor-pair reuse.
- `checked_bounded` proves language coverage at every finite accepted height.
- `checked_sound` proves coverage of every finite accepted term.
- `check` executes the identity check, ancestor check, universal narrow-edge
  loop, existential wide-edge loop, label test, unconstrained-cover test, and
  same-arity child comparison. Fuel exposes finite successful runs.
- `check_certificate` and `check_sound` prove every successful bounded search
  has the required coverage. The structural EmptyNode early returns are
  omitted from this semantic comparison core. They are sound empty-language
  shortcuts. This module does not claim byte-for-byte source extraction.
- `retained_union_exact` and `checked_filter_exact` prove that the source's
  retained-recursive-operand filter preserves the union language whenever
  the accepted comparison has that coverage.

The graph interface is the closed outgoing-edge view. Its interpretation of
physical recursive nodes, the meaning of `noConstraint`, and termination of
the unbounded Haskell comparison remain explicit source contracts. Ancestor
reuse itself needs no guardedness or totality axiom: acceptance is the least
finite-run semantics, and the proof decreases accepted term height.

`MergedAlternativesGroups`:

- `columns_cover` derives coverage by the column unions from each original
  accepted row.
- `mergeGroup_covers` covers both source group branches, including singleton
  guard retention and multi-edge guard removal. It requires coverage from
  the child merge calls. It does not assume exact child equality.
- `nullary_guard_widening` uses distinct semantic guards and proves that its
  two input edges differ. Both guards reject the nullary term. One guard
  accepts a unary term, which proves the edge inequality even though this
  term has the wrong arity for either edge. Thus duplicate-edge removal
  cannot remove this semantic group witness. The source probe separately
  checks the distinct raw guard syntax described above.

`MergedEqualityReduction`:

- `merged` inserts the merge after each peer projection.
- `classEdits_eq` gives exactly the new target schedule.
- `merged_laws` derives all existing reduction laws from the previous local
  contracts and a language-superset merge contract.
- `constrained_pass_exact` proves the new full single pass preserves the
  original constrained forest language.
- `constrained_reduce_exact` proves the same for any completed repetition.
  It does not assert that the repetition completes.

`MergedAlternativesRecursion`:

- `childColumn_eq` computes the offending `[A, B]` column.
- `legacy_no_completion` proves that the two mandatory legacy call sites
  have no finite dependency tree.
- `repaired_completion` gives the finite dependency tree after the guard.

This last module models the concrete call dependency slice. It is not an
interpreter for all Haskell evaluations or an extracted interning machine.

`MergedRawLeaves`:

- `top` constructs the new unconstrained row inside the existing finite
  source inventory.
- `merge` retains one exact row or replaces multiple distinct rows with Top.
- `unique`, `support`, `unchanged`, and `idempotent` describe that row operation.
- `covers` proves semantic coverage when Top holds.
- `merged_target_progress` reuses the derived source rank for intersection
  against the merged target. This is a local progress result.

`MergedRowGroups` and `MergedRawLeafSource` now supply the physical leaf step:

- `represented_rows` reads the original raw guards from the actual outgoing
  complete edge records. `represented_rows_distinct` derives that the canonical
  input contains no repeated complete raw row. The proof uses actual edge
  identity normalization and coherent edge records.
- `declarations_member` proves that grouping those physical records selects
  exactly `MergedRawLeaves.merge`. Grouping counts distinct raw guards, not
  semantic guard equivalence. The singleton keeps its raw spelling.
- `worker` executes the actual nullary `makeEdge` and `makeNode` requests.
  `worker_eq_raw` proves that no sentinel or rejected request can occur here.
- `worker_keys` derives the exact output key set. `worker_record` derives
  complete-record equality in a common later cache. `worker_available`
  preserves all runtime cache facts.
- `worker_completed` constructs a finite proof cache for the compiled output.
  `worker_actual` pulls that representation back to the actual runtime output
  cache. Thus the next runtime operation needs no proof-cache entries.

The symbol order is explicit. It must cover every physical input symbol.
It may be the actual HashMap order. A fixed finite symbol enumeration also
works; unused symbols issue no request. Complete-record correspondence does
not depend on the selected order. The grouping model deduplicates complete
raw rows explicitly; the canonical-input theorem derives that this cannot
change the branch on a represented source leaf.

All seven modules build with Lean 4.34.1. Include them in the root audit
before claiming a complete audit pass.

## Correspondence boundary after the source refresh

The old `EqualityLeafProjectionSnapshotTargets.target` reads and intersects
peer projections without a merge. It therefore does not model the current
target worker on unrestricted raw leaves. For example, two different rows
at the same nullary symbol now become one Top row before intersection.

The existing raw constructor, intersection, union, finite-inventory, and
local intersection-progress proofs remain valid for their stated workers.
The new `MergedProjectionTargets` reads peer projections, merges each
physical leaf, and applies the seeded intersection in actual runtime caches.
`MergedProjectionClass`, `Schedule`, `Pass`, `Termination`, and `Bound`
compose the complete projected-leaf schedule. `compiled_bound` derives
termination within the original occurrence weight plus one and a final
allocation-free fixed point. It retains normalized proper paths and leaf
endpoints, and requires complete symbol order for physical grouping.

This covers the physical merged leaf worker and schedule. It does not prove
unrestricted recursive merging or nested-endpoint fixed schedules. The
finite semantic graph view, host evaluation, containers, and Haskell extraction
remain separate correspondence obligations. The full Lean audit passes
846 jobs and 33,461 theorem dependency checks.

Keep the earlier nonassociativity and schedule counterexamples. Do not claim
that an old schedule replay still reproduces the new merged-target schedule.
The merged projected-leaf termination theorem does not supply an unrestricted
nested-endpoint or recursive schedule termination proof.
