# Merged equality narrowing

Updated: 2026-10-13. Current source: `4897831`, including PR98.
Earlier checkpoints below identify the previous single-edge merge policy.

## Source change

`reduceEClass` now calls `mergeAlternatives` on every peer projection before
the target intersection. The merge groups ordinary edges by symbol and arity.
It preserves every root edge and constraint when the group has at most four
distinct edges. It drops the root constraints when a group has more than four
edges and unions the children at each position. Both branches process children.

A preserved small root group can still enlarge its language when a descendant
group is merged. Exact preservation of a small group requires exact child
transformations. Nullary small groups preserve their complete original records.

This is an overapproximation. It can enlarge a language even at arity zero or
one, because it drops constraints. The complete equality reduction can still
preserve its language: the original edge constraints remain, and each edit
intersects the original node with the enlarged peer target.

## Repaired recursive call cycle and historical witness

Before PR98, the smallest example used two recursive operands.
Let `A = mu x. {a(), f(x)}` and `B = mu y. {b(), f(y)}`. Both are closed and
productive. `union [A, B]` exposes four alternatives, including `f(A)` and
`f(B)`. Merging those two alternatives calls `mergedUnion [A, B]`. Both
recursive operands survive the filter. The old multi-operand branch then
calls `mergeAlternatives (union [A, B])` again.

The focused source probe timed out after three seconds before the repair.
The same failure occurs when the recursive children are retained
`InternedUnion` values. A guard that checks only `InternedMu` does not cover
that second case.

The upstream repair changes the multi-operand branch:

- If a retained operand satisfies `recursiveBoundary`, return `union others`.
- Otherwise, continue with `mergeAlternatives (union others)`.
- Keep the singleton branch unchanged.

The branch can expose a recursive union once. It does not recursively merge
that exposure. Thus it does not reproduce the same merge request. The result
can retain multiple alternatives below that boundary. The Haddock now states
this limit. Its edge-pairing bound applies at a merged ordinary root; it does
not claim a bound by the smaller input or a bound below recursive boundaries.

PR98 now preserves that two-edge group. The retained current probe uses five
recursive operands with different base leaves. Their five `f` alternatives
enter the large-group branch and produce the same recursive child-union
request. The repair remains necessary. `MergedAlternativesThreshold` records
this current five-operand branch and its finite repaired dependency tree.

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

The earlier two-operand probes timed out before the repair. They are historical
evidence for the old policy. The current invocations use five recursive
operands and assert that their five `f` edges become one. All eleven checks
pass in both modes. Each mode checks 54 unary terms through eight `f`
constructors and the constrained parent caller.

The current nullary probe uses five distinct false raw guards of the form
`Not (Or (replicate n Top))`, for `n` from one through five. Four guards retain
the exact original node. Repeated copies of those four guards do not trigger a
merge. Five distinct guards become one Top row and admit the previously
rejected nullary term. A singleton parent with that five-row child demonstrates
that the small-group branch still processes its children.

Fourmolu formatting passed. Both current probe modes passed in
`/tmp/mcfta-20261013-four-edge-merge-replay.log`. All 620 existing Haskell examples
passed after the source refresh in
`/tmp/mcfta-20261013-upstream-refresh-tests.log`.

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
- `mergeGroup_covers` covers both current branches. At most four root edges
  keep their guards; larger groups collapse to an unconstrained edge. The
  result is a list because a small group can retain multiple edges.
- `mergeGroup_bound` proves at most four output edges per symbol/arity group.
  `mergeGroup_small` gives exact root-edge retention and child transformation.
  `mergeGroup_identity` proves exact small-group retention for identity child
  transformations. Coverage alone does not imply exactness.
- `legacyMergeGroup`, `legacyMergeGroup_covers`, and
  `legacy_nullary_guard_widening` retain the previous policy and its two-edge
  semantic witness. They do not describe PR98.

`MergedAlternativesThreshold`:

- `four_rows`, `five_rows`, and `duplicate_rows` check the exact boundary and
  complete-row duplicate handling.
- `rejecting_distinct` and `five_guard_widening` give a current semantic
  witness with five distinct edge guards, each rejecting the nullary term.
- `recursive_group_merges` checks that five recursive alternatives enter the
  current merged branch. `five_without_repair` retains the resulting call
  cycle obstruction, and `five_repaired` gives its finite dependency tree.

`MergedEqualityReduction`:

- `merged` inserts the merge after each peer projection.
- `classEdits_eq` gives exactly the new target schedule.
- `merged_laws` derives all existing reduction laws from the previous local
  contracts and a language-superset merge contract.
- `constrained_pass_exact` proves the new full single pass preserves the
  original constrained forest language.
- `constrained_reduce_exact` proves the same for any completed repetition.
  It does not assert that the repetition completes.

`MergedAlternativesRecursion` retains the historical two-edge policy:

- `childColumn_eq` computes the offending `[A, B]` column.
- `legacy_no_completion` proves that the two mandatory legacy call sites
  have no finite dependency tree.
- `repaired_completion` gives the finite dependency tree after the guard.

This last module models the concrete call dependency slice. It is not an
interpreter for all Haskell evaluations or an extracted interning machine.

`MergedRawLeaves`:

- `top` constructs the new unconstrained row inside the existing finite
  source inventory.
- `selected` enumerates the distinct selected complete rows. `merge` uses the
  literal length threshold: at most four rows stay; more than four become Top.
- `selected_distinct`, `small_exact`, `support`, `unchanged`, and `idempotent`
  describe the current operation. `merged_bound` proves at most four distinct
  output rows per symbol. The previous one-row uniqueness claim is false for
  preserved groups of two through four rows and has been removed.
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
  semantic guard equivalence. Every small-group row keeps its raw spelling.
  `rowsAt_perm` derives equality of the physical and finite-carrier distinct
  row counts, so the threshold premise is not assumed.
- `worker` executes the actual nullary `makeEdge` and `makeNode` requests.
  `worker_eq_raw` proves that no sentinel or rejected request can occur here.
- `worker_keys` derives the exact output key set. `worker_record` derives
  complete-record equality in a common later cache. `worker_available`
  preserves all runtime cache facts.
- `worker_completed` constructs a finite proof cache for the compiled output.
  `worker_actual` pulls that representation back to the actual runtime output
  cache. Thus the next runtime operation needs no proof-cache entries.
- `worker_group_bound` proves the four-row bound on the actual returned
  physical records. `worker_small_record` proves complete-node equality when
  every input nullary group has at most four distinct rows.

The symbol order is explicit. It must cover every physical input symbol.
It may be the actual HashMap order. A fixed finite symbol enumeration also
works; unused symbols issue no request. Complete-record correspondence does
not depend on the selected order. The grouping model deduplicates complete
raw rows explicitly; the canonical-input theorem derives that this cannot
change the branch on a represented source leaf.

The current threshold modules and the downstream projection order, language,
pass, termination, and bound modules build with Lean 4.34.1. Add the new
`MergedAlternativesThreshold` import before claiming a complete audit pass.

## Correspondence boundary after the source refresh

The old `EqualityLeafProjectionSnapshotTargets.target` reads and intersects
peer projections without a merge. It therefore does not model the current
target worker on unrestricted raw leaves. For example, five different rows
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
remain separate correspondence obligations. The previous full audit passed
849 jobs and 33,472 theorem dependency checks before this threshold refresh;
those figures are historical evidence.

`MergedProjectionOrder.observed_complete` derives a complete symbol order
directly from actual outgoing rows. `same_record` proves that any two complete
orders produce the same full merged record in a common valid cache.
`MergedRawLeafLanguage.worker_covers` derives language coverage from the
physical input and output rows for every nullary guard interpreter that
accepts Top. The general recursive physical coverage bridge remains open.

`MergedSubsumptionTermination.check_saturated` proves that the executable
coverage checker stabilizes once its fuel reaches the number of remaining
pairs in a complete finite inventory. The proof removes each new pair and
adds it to the ancestor list. Establishing such an inventory for arbitrary
physical recursive unfolding remains a separate source obligation.

Keep the earlier nonassociativity and schedule counterexamples. Do not claim
that an old schedule replay still reproduces the new merged-target schedule.
The merged projected-leaf termination theorem does not supply an unrestricted
nested-endpoint or recursive schedule termination proof.
