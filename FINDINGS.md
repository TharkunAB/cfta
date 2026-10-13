# Current formalization findings

Updated: **2026-10-14 01:08 CEST (Europe/Stockholm)**.

## Current result

The main Sized contract is proved in the source models: exact distinct
accepted terms at each node-count size, finite class evaluation, size-major
enumeration, and both rank/unrank inverse laws. The reference, solver-decided,
and optimized paths have the same required sequence. The latest proofs use
the actual original-state finite map, not an assumption that the state type
itself is finite. **Whole Haskell implementation verification remains open.**

`SourceSizedFiniteKeys*` derives root/child membership from FTA validation,
finite key restriction, exact raw rows, dense canonical order, actual trim
keys, and complete functional and relational bounded-fold readback.
`SourceSizedFiniteKeysDispatch.nativeSized_eq` proves exact raw-map dispatcher
agreement, including errors and all four query functions. The raw synchronous
product minimum calculation and its finite convergence are derived.

`TablePositionCountBound.positions_congr` now proves that bottom-up ranking
reads counts only through the input term's node count. This includes earlier
transition offsets. `TablePositionFiniteEvaluation.finite_rank` constructs
finite count and child-state tables with the exact original rank or failure.
`SourceSizedFiniteKeysRankEvaluation.native_rank_laws` connects that finite
computation to the actual optimized public query and both signed inverse laws.
The state type can be infinite. Concrete Haskell lazy scheduling remains open.

`SourceSizedFiniteKeysNativeLiquid.encoded_correct` proves independent
mixed-sort ambient logical acceptance, original canonical order, complete
bounded prefixes, distinctness, and both signed inverses for the actual raw
fold. `encoded_finite` derives finite outcomes from finite external attempts.
Unknown and unchanged exceptions remain separate. Replies need not be stable.
External Sat/Unsat correctness and completion remain explicit contracts.
See [finite map Sized](lean/notes-sized-finite-keys.md).

## Repairs and retained counterexamples

- **`73223201`: quantified SMT name capture.** Liquid Fixpoint mapped raw
  names `1` and `fix$1` to the same symbol. A false quantified entailment
  returned Yes. The adapter now uses one injective safe encoding for all
  declarations, variables, function heads, binders, and the default value name.
  The codec, serializer control, complete quantified meaning, preflight, and
  public liquid composition are proved. Native and Lean counterexamples
  remain. See [solver names](lean/notes-solver-name-encoding.md).
- **`a8b32869`: weighted-search midpoint overflow.** The former Int index sum
  can wrap even when both indices fit. The repair uses
  `low + (high - low) quot 2`. The repaired full search requires only a
  representable array length. The historical 64-bit example is an arithmetic
  boundary, not a feasible allocated-array failure. See
  [weighted selection](lean/notes-quickcheck-frequency.md).
- **`17b21453`: cyclic custom-key order qualification.** Equal complete sort
  keys retain source row order. Noninjective custom symbol keys can exchange
  ranks when interning order changes. Counts and both inverses still hold.
  Source comments and Lean/native evidence now state the exact limit.
- Earlier source repairs and counterexamples remain, including direct-row
  Sized dispatch, implicit ambient fresh-name capture, recursive child unions,
  fresh ordinary probes, and the disproved saturated-merge shortcut.

## Other completed source bridges

`SourceInternedRows*` proves finite shared row traversal, ordered constraints
and child readback, guarded language, validation, and issued-cache exposure.
Dense numbering and finite-key minimum sizes are derived. Cyclic query and
sampler records have exact counts, decoder positions, reciprocal masses,
normalization, support, PMFs, and sampled rank replay. No arbitrary sampler
normalization premise remains. Distinct terms, accepting runs, generator
members, and aggregated PMF keys remain separate concepts.

`SourceInternedIntersectionDispatch*` proves ordinary native empty/self/order
control, actual constructor effects, finite completion, and completed memo
results with concrete execution provenance. `SourcePhysicalSharedRows*`
connects actual cache readback and traversal to the minimum callback. The
finite plain callback detects exactly the original operands' shared terms
without a product-row or global child-meet premise.

`SourcePhysicalRecursiveRows*` proves actual repaired unfolding, precise cache
effects, stable replay, and shared rows for `mu x. (base | step x)`. It derives
that fragment's independent language of finite Chain terms from an available coherent
stored knot. `SourcePhysicalRecursiveConstruction` now supplies that knot from actual repaired
empty-cache construction for arbitrary base and step symbols. It derives exact
records, counters, coherent availability, constructor replay, unfolding, and shared
rows. `SourcePhysicalRecursiveSized.source_sized` connects those source-derived
rows to one distinct term at every positive size, finite class evaluation, distinct
size-major prefixes, and both inverse laws. General Mu/union construction and
exposure remain open. See [physical intersection](lean/notes-physical-intersection-rows.md).

`InternedDepthFreeProjection*` proves full-syntax free-name membership
agreement and actual ordinary-root callback deep observations with nested
children. General cached-depth and binder-heap induction remain open.

`EqualityNestedUnaryAncestorRoot*` composes actual projections, target merges,
both ancestor edits, and the root identity stop. The fixed unary/two-atom,
one-class fragment terminates within `4 * (left + right) + 2` passes and
retains exact output/cache for additional fuel. All marked drafts retain their
bytes. See [the equality root proof](lean/notes-equality-nested-unary-root.md).

Earlier bounded import, liquid denotation, finite reconstruction, observation
groups, weights, sampling, PMFs, CPS enumeration, union-find, and memo-domain
proofs remain. The detailed notes and API coverage ledger record their scope.

## Remaining work and assessment

The central mathematical and source-algorithm contracts are strong. The work
has exposed and repaired real defects. It is not yet an end-to-end proof of
the Haskell library. The largest remaining obligations concern general
recursive construction/exposure, pending lazy memo values and full recursive
memo traces, native SCC/split import readback and custom decoder order,
general equality propagation, and concrete runtime/dependency contracts.
No verified Haskell-to-Lean extraction exists. There is no honest single
completion percentage for these different layers.

## Checkpoint and validation

Branch: `formalization/microcfta-sized-20261014`.
Upstream base: `origin/microcfta` at **`f59c198d`** (PR #116).
The 398-step rebase completed at `97d79d63`. Two overlap resolutions retain
upstream's equivalent `void` call and merged recursive-union changelog text.
Backup `backup/formalization-before-sized-refresh-20261014-0036` retains `f4b5fac1`.
All 1,515 saved Lean-tree files matched immediately after rebase. Later only
intended coverage documents, the finite-key note, and audit imports changed among those files.
All earlier proofs, marked drafts, repairs, stashes, and worktrees remain.
`lean/repro/NestedUnaryTwoAtom.hs` remains intentionally untracked.
The latest proof checkpoint is **`93f3cbaa`**; later commits record this handoff.

The current Lean 4.34.1 audit passes **1,185 build targets and 39,846 theorem
dependency checks**, using only `propext`, `Classical.choice`, and `Quot.sound`.
Log: `/tmp/mcfta-recursive-20261014-audit.log`.
After the upstream refresh, all **640** examples passed in Nix: 288 core, 208
generator, and 144 refinement. Fourmolu and cabal-gild passed. No new production
test was added locally. Exact commands and logs are in [HANDOFF.md](HANDOFF.md).

No background proof worker is active. Weekly allowance was **35% at 01:08 CEST**.
Refresh it before new work and stop all work at **1% or less**, as the latest
explicit user instruction requires. Everything remains local: no push, deployment, or
board post. Benchmark formalization remains excluded.

## Previous Sized checkpoint

The following 21:56 record is historical. The results above and the current
handoff supersede its next-target and publication statements.

Updated: **2026-10-13 21:56 CEST**.

The primary `Data.CFTA.Sized` source models now cover exact accepted terms at
each node-count size, finite class evaluation, size-major prefixes, and both
distinct-term rank/unrank inverse laws. The decided path preserves the first
Unknown error and requires explicit per-call evaluator contracts. Replies
to repeated queries may differ. Every successful relational trace is exact
under per-call adequacy. Finite per-call result witnesses give a finite
bounded result, including errors.
**Whole-implementation verification remains incomplete.**

Upstream refresh reported no change: `origin/microcfta` remains **`2200117`**.
The starting checkpoint `f8a3d48` is preserved on
`backup/formalization-before-sized-resume-20261013-2123`. All earlier proofs,
counterexamples, repairs, three marked drafts, stashes, and other worktrees
remain. The untracked `lean/repro/NestedUnaryTwoAtom.hs` is unchanged.

## Current exact-size results and repair

Two native and kernel-checked examples show that the former optimized Sized
path changed ranks. `fromFTA` can remove dead or duplicate transitions, which
can change canonical row order. Checking that trimming changes nothing does
not cover the duplicate case.

Local repair **`ea73724b`** sends the original sorted explicit rows to the
existing optimized count table and bottom-up inverse. It checks ambiguity
with a finite synchronous product. Constrained or ambiguous graphs use the
reference. The interned core remains intact. `SourceSizedDispatcher.sized_eq_reference`
proves equality of the complete query records and residual errors for the two
branches. This direct query path no longer depends on `fromFTA` or `rowsOf`.

The checked reference recurrence includes actual candidate order, equality
path traversal, first-occurrence duplicate removal, finite evaluation, signed
invalid queries, and the residual scan on trimmed rows. Successful decided
tables preserve the exact original reference order through their bound.
Empty classes do not suppress later sizes. `SourcePlanScale` extends the
existing partition proofs with positive repeated-child node counts.
`BoundedPruningFix` and `BoundedPruningCaller` prove the current local loop
bounds and preservation under explicit per-call contracts.

Read [the Sized proof note](lean/notes-source-sized.md) for the theorem map,
both order counterexamples, source repair, validation, and exact boundaries.
The source models do not verify concrete Haskell containers, lazy heaps,
machine conversions, solver IO, or extraction.

The aggregate audit passes **1,052 jobs and 37,335 theorem dependency checks**.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Log: `/tmp/mcfta-sized-20261013-final-audit.log`.
The generator suite passed **206 examples**, including two temporary
regression cases. The permanent suite remains unchanged at 204 examples.
Both native counterexamples are retained. Fourmolu and cabal-gild passed in
Nix. No new production test case was committed. Counts are validation
evidence, not a coverage percentage.

All proof workers are stopped. All work remains local. Weekly allowance was **58% at 21:55 CEST**; refresh it
with `/tmp/mcfta-weekly-usage.py` and stop all work at 20% or less.
[HANDOFF.md](HANDOFF.md) and [NEXT-PROMPT.md](NEXT-PROMPT.md) contain the current
restart instructions. The preserved constructor and equality work remains
secondary to the direct exact graph contracts.

## Previous restart review: source wishlist and initial proof gaps

This section records the `f8a3d48` restart review before the local Sized repair.
Its next-target statements are historical. The current results above and the
Sized proof note supersede them.

PRs #107, #109, #110, #111, #112, and #113 address most of the source wishlist.
The explicit-graph decision keeps the optimized interned core. It does not
authorize or require a replacement of that core.

| Main contract | New implementation | Checked foundation and next gap |
| --- | --- | --- |
| Exact distinct terms at size `n` | `Data.CFTA.Sized.sizedReference` builds child classes at smaller sizes, checks path equalities, and removes duplicate terms. It supports cyclic and ambiguous graphs. | `RecursiveSize` proves exact-size recurrence for plain graphs; `Language` proves guarded acceptance; `DistinctRank` proves distinct indexes. Compose a new proof for the actual equality-filtered, first-occurrence source sequence. |
| Finite time for each requested size | The reference recurs only on smaller sizes. `sizedUpTo` folds over finitely many sizes and states. Empty classes do not stop later sizes. | Formalize these actual workers. Solver-decided completion requires each evaluator call to terminate. A proof of reference recurrence does not establish lazy source productivity or optimized adapter completion. |
| Size order | `termsOfSize`, `countOfSize`, `rankOfSize`, and `unrankOfSize` share one class sequence. PR #111 counts repeated child positions by node multiplicity. | Compose ascending classes into the size-order theorem. Extend source size models for `PlanScale`. Existing `terms` remains depth/marker oriented; finite `fromAutomaton` retains its own rank order and symbolic size conventions. |
| Ranking and unranking | Reference queries use the same distinct list. `sized` dispatches to the count-table decoder and bottom-up inverse where the plain unambiguous import succeeds. | Reuse `SourceCyclicAutomaton.exact_index_api`, `SourceFiniteAutomaton.exact_index_api`, and `SourceSymbolicStableIndex.stable_source_index`. Prove exact order agreement and current representation adapters for the new dispatch. |
| Full guards at a size bound | `sizedUpTo` checks each complete candidate with `evaluateConstraint`. `Unknown` gives `GuardUnknown`; it does not reject a term silently. Returned classes above the bound are empty. | Prove successful exactness under terminating and adequate evaluator contracts. Logical solver soundness alone does not prove complete decisions. |

Read [Sized.hs](microcfta-generator/src/Data/CFTA/Sized.hs) and
[ADR 0004](docs/adr/0004-explicit-graph-boundary.md). `sizedReference` and
`sizedUpTo` operate directly on an explicit `FTA` without pruning or binder
construction. The optimized `sized` branch still calls `fromFTA`, then
`automatonIndex` and `automatonTermPosition`; those read interned rows.
The ADR identifies consolidation through `toFTA` as further work. It is not
evidence that every optimized query already avoids the interned adapters.

PR #109 adds `fixWithin` and `pruneRounds = 64`. Transition narrowing and
repeated recursive-node pruning now have local pass limits. Original guards
remain when the limit ends. This removes the requirement to reach an identity
fixed point in those loops. It does not by itself prove every individual
pass, recursive reconstruction, or solver call terminates. The explicit graph
reference/decided size paths do not call these loops at all.

PR #110 gives three source contracts in `CONTEXT.md`: exact transformation,
over-approximation, and representative selection. The saturated-merge
counterexample remains valid. Monotonicity of that approximation is not a
prerequisite for the direct exact-size API. The old proof drafts remain useful
for the interned and optimization paths; they are secondary restart targets.

## New representation bridges

| PR | Source change | Required proof |
| --- | --- | --- |
| #104 | Enumeration now uses continuation-passing backtracking. | Relate `allBranches` to the `StateT`/list machine in `EnumerationState`. Preserve ordered results, branch-local states, failure, choice, bind, and state operations before transferring `EnumerationExact.runs_exact`. |
| #105 | One fold descends suspended constraints into every child. | Relate each resulting `IntMap` entry to `EqualityTrie.descendScs_exact`. Compose inherited/new constraints and prove the maximum-child arity check. Valid tries must exclude empty child entries. |
| #106 | Union-find omits a compression write when the parent is already the representative. | Transfer `UnionFind.findRoot_correct` and termination through extensional forest equality. |
| #108 | The empty intersection domain has identity zero; other domain identities are raw interned identities plus one. | Adapt `IntersectionFlatMemoKeyDomain.domain_intern_correct`, `domain_identity_exact`, and flat-key injectivity. Prove zero/successor separation and revised machine bounds. |
| #111 | `PlanScale` and `scaleIndex` multiply a member's size by a positive factor without changing its rank or value. | Extend `SourcePlanPositions.Plan`, `position_replay`, and `SourcePlanPartition.partition_exact`. Use `CompactGroups.childGroups_nonempty` for a positive factor. Selection is restricted to valid counted sizes; quotient selection alone does not check divisibility. |

The source review found no new concrete public correctness defect in these
five changes. Their former models still check, but they do not include the
new representation branches. `CompactEdgeRanks` count, language, and inverse
results remain reusable; the repeated-child node-count connection needs the
new scaling proof. No new production test was added in this refresh.

## Preserved component coverage

| Area | Checked result | What remains |
| --- | --- | --- |
| Mathematical language, enumeration, ranks, probabilities | Finite-term acceptance, enumeration laws, distinct-term bijections/inverses, and exact rational distributions. | Full connection of every runtime API path to these laws. Generator members remain distinct from FTA terms. |
| Executable library components | Enumeration and symbolic count/select/rank drivers, supported lattice operations, typed recursive/mutual/n-ary families, nested joins, guard and pruning components. | Arbitrary runtime schemas, support/codec wiring, recursive productivity, and remaining primitive adapters. |
| Constructor repair | Facts, normalization, actual semantic origins, root profiles, free-name heaps, closed-output free-name absence, capture bounds, exact completed replay, and bounded source chooser correspondence. | General repaired first-run completion; full depth/deep heap induction; complete accepted-language and arbitrary substitution correspondence. |
| Cold comparison and merging | Prepared cold completion, original-language coverage, exact fuel stability and successful replay. Exact repaired reader and complete comparator bridges. | The repaired selection bridge has a kernel-timeout draft; whole repaired merge composition follows it. Open nested Mu reconstruction remains outside the prepared fragment. |
| Equality convergence | Repeated target merge reaches an exact fixed point within ordinary-tree height. A concrete nested unary two-atom endpoint loop has a derived bound. Actual-cache original ancestor replay and edit effects are proved. | Compose both ancestor/forest edits and root stopping. Generalize beyond fixed unary/two-atom/single-class fragments. |
| Upstream optimizations through PR #103 | Flat memo probing/copy/growth/winner retention and bounded keys; maintained enumeration indexes and exact scheduler selection. | The newer representation bridges above, native publication, concrete containers, identity lifetimes, and runtime range obligations. |

See [COVERAGE](lean/COVERAGE.md) and [API-COVERAGE](lean/API-COVERAGE.md)
for precise premises. External solver, random-source, codec, concurrency,
and Haskell runtime contracts are explicit. There is no verified extraction.

## Closed constructor defect and local repair

The old constructor's unrestricted closed completion claim is **false**.
`InternedClosedPendingBoundary` gives a scoped structural expression that
reaches pair `(86,86)`, reserved identity 87, and an absent payload with next
counter 92. Its callbacks do not inspect their arguments. Two independent
native translations exceed five seconds while forcing the root to WHNF.
The native runs establish bounded noncompletion; the kernel separately proves
the exact model pending result. This is row 23 in the repair ledger below.

Local repair **`fbc3097`** (formerly `e0e1b37`) chooses an ordinary probe above every free ordinary
level of the actual Depth observation. `matchMu` uses that same stored
observation. Both failing fixtures complete in the repaired Lean executor.
All five native probes and 620 examples passed at the earlier checkpoint.
The rebased combined suites now pass 633 examples.
The old executor and counterexample remain intact.

The repaired source proofs now retain all callback effects, including discarded
computations. Each complete Mu's free ordinary names match those of its Depth
observation and lie below the chosen probe. Returned-value freshness alone does
not settle all intermediate discarded computations. General repaired completion
is still open. Read [the counterexample](lean/notes-paired-pending-boundary.md),
[repair](lean/notes-fresh-ordinary-candidate.md),
[semantic contexts](lean/notes-fresh-ordinary-contexts.md), and
[depth work](lean/notes-deep-free-depth.md).

The second local repair, **`807e867`** (formerly `558b316`), preserves explicit recursive child
unions and fixes the five-alternative public pruning timeout. It remains
separate from the constructor repair. See row 22 and
[merged narrowing](lean/notes-merged-narrowing.md).

## A rejected general convergence argument

Saturated target merging is **not monotone** under language inclusion or
source childwise row coverage. Five explicit pairs and a compact two-row
encoding have the same five native accepted terms. Both merge results are
already fixed points, but one accepts nine pairs and the other five.
`p(a,c)` separates them.

`EqualityMergedTargetMonotonicity.saturation_not_monotone` proves input
inclusion and failed output inclusion using the actual returned-cache language.
Native execution independently confirms input equality and the `5 → 9` versus
`5 → 5` counts. This rejects a proposed closure proof. It does not demonstrate
an equality-loop cycle or prove nontermination. Preserve the
[counterexample and explanation](lean/notes-equality-merged-monotonicity.md).

## Exact restart targets

1. Prove the new `Data.CFTA.Sized` reference class worker and its four query
   laws. Add the bounded decided path and its explicit evaluator contracts.
2. Connect the optimized dispatch to the same sequence. Prove size-major
   composition and the explicit-graph adapter boundary.
3. Add positive `PlanScale` correspondence and the bounded pruning caller.
   Complete the small representation bridges listed above where needed.
4. Resume the preserved constructor and optimization targets below when the
   exact path requires them or after its main contracts are complete.

Detailed instructions are in `HANDOFF.md`. The previous restart targets are
retained here as secondary work:

1. Finish free-name membership projection for `InternedDepthSemantics`.
   Coherence and exact profile projection already compile. Use the local
   `InternedFreshOrdinaryDepthRequest` law in full syntax induction over literal
   environments to derive the depth/deep heap. Then continue general completion.
2. Resume `MergedFreshOrdinarySelection.lean.incomplete`. Its `any_eq` proof
   exceeds the kernel limit; the complete comparator bridge is checked. Then
   compose repaired selection through the cold merge worker. See
   [comparison bridge](lean/notes-fresh-ordinary-comparison.md).
3. Resume `EqualityNestedUnaryAncestorEditCompletion.lean.draft`. Retain the
   exact `node_complete` run, apply `edit_stored` and `meet_correct`, then compose
   both forest edits and the root identity stop test. See
   [actual-cache ancestor replay](lean/notes-equality-nested-unary-ancestor-replay.md).
4. Continue the broader runtime, accepted-language, and termination obligations.
   Do not infer progress from a finite carrier alone or use the refuted
   saturated-merge monotonicity shortcut.

The original `MergedAdaptiveStability.lean.incomplete` remains byte-for-byte
unchanged. Its completed sibling proves fuel independence. Both newer marked
drafts are committed and excluded from builds. The positive diagnostic
`lean/repro/NestedUnaryTwoAtom.hs` remains deliberately untracked; preserve it.
All stable modules are in the aggregate audit.

The sections below retain the detailed repair ledger and earlier component
results. Old constructor modules describe the preserved pre-repair executor
unless their names explicitly start with `InternedFreshOrdinary`.

## Previous checkpoint and required contract

The history below describes the checkpoint before PRs #104–#113. Its source
hashes and dated checks remain historical evidence. Use the current status
and restart priorities above for new work.

The continuation branch is `formalization/microcfta-resume-20261012`.
Its implementation base is `origin/microcfta` at `9508eb3`, including
PRs #97 through #103. The latest continuation rebased all 308 commits.
The earlier reset continuation rebased 274 commits onto `4897831`.
Source conflicts kept the merged upstream implementations and all local proofs.
Backup `backup/formalization-before-refresh-20261013-1306` retains the
published checkpoint `8a80947`. The rebased proof tree initially matched it
exactly. The earlier restart rebased 267 commits onto `8ac24bb`. Backup `backup/formalization-before-refresh-20261013-0418` retains
the previous checkpoint `2aacf4f`. Proof commit `721ff6d` adds full free-name
semantics and historical probe boundaries. The previous proof branch remains
unchanged. Backup `backup/lean-before-microcfta-20261012-2200` and the retained
stash preserve the pre-rebase work. Matti explicitly requested publication of checkpoint `8a80947`; it was
pushed to `formalization/microcfta` at 04:33 CEST. New work remains local.
For a constrained language, compilation and enumeration must contain every
valid finite term and no invalid term. A finite FTA language with `n`
distinct terms must have exactly `n` ranks, with both decoder/inverse laws.
Sampling must give each term its requested normalized weight. An exact
optimization must preserve both the accepted language and the weights.

Three counts must remain separate:

- A **term** is one finite ordered constructor tree.
- A **run** is one accepting derivation. Several runs can produce one term.
- A **generator member** is one indexed source occurrence. Several members
  can have equal values and equal constructor terms.

The distinct-term rank contract applies to the FTA import path. Arbitrary
generator choices, maps, and joins retain members. They are not a quotient
by term or value equality. The checked recursive example
`label N (choice [pure, occurrence, occurrence])` has two size-two member
ranks with the same complete constructor term. Its inverse correctly returns
both ranks. This is a contract distinction, not a new decoder defect.

## Repaired source defects

Rows 1 through 21 are merged upstream at `4897831`. Rows 18 through 21
were local repairs at the earlier checkpoint. Rows 22 and 23 are local repairs. Each row has a retained source reproduction and a corresponding formal
counterexample, repair theorem, or operational model. Older per-repair test
totals in the linked reports describe their historical checkpoints. The
current combined suite total is 633.

| # | Failure before the repair | Current behavior and evidence |
| --- | --- | --- |
| 1 | Quantified substitution could capture a name in an `App` function position and change `No` to `Yes`. | Rename bound function heads and substitute nullary applications as values. Reject an unrepresentable non-name function head through the checked API. [Reproduction](lean/repro/FormulaCapture.hs). |
| 2 | A tautological observation of an atomic 9:1 choice could make bounded sampling uniform after a product. | Retain within-size atomic weights and transport their size metadata. [Reproduction](lean/repro/CurrentFindings.hs); `MassRetention`, `SizeMass`, `SizeTransport`. |
| 3 | Minimization could delete the only accepted root term without installing its chosen representative at the root. | Install root representatives and recheck an accepted derivation after the complete schedule. [Detailed finding](lean/SYSTEM.md#minimization-can-remove-the-only-accepted-root-term); `MinimizeSchedule`. |
| 4 | Union inside a nested binder could discard an enclosing reference and omit valid finite terms. | Retain open union operands and resolve their epsilon closure after binding. [Reproduction](lean/repro/OpenUnion.hs); `EpsilonUnion`. |
| 5 | Pruning a valid open nested binder could raise `nodeEdges: unresolved union reference`. | Inspect the stored open body before unsafe outer-edge unfolding. [Reproduction](lean/repro/PruneOpenBinder.hs); `PruneReads`. |
| 6 | Closing grouped applications could produce support graphs that rejected every decoded term. | Close every retained private alternative and preserve the complete callback image. [Reproduction](lean/repro/GroupedSupport.hs); `SupportAlternatives`. |
| 7 | Constructor and application closing could remove private nodes across a recursive occurrence boundary. | Use one private `Recursion` boundary consistently in support, inspection, terms, and inverse ranking. [Reproduction](lean/repro/RecursiveSupport.hs); `RecursiveSupportBoundary`. |
| 8 | Grouped function spines could lose correlation between their retained child alternatives. | Preserve correlated function prefixes while closing the support and inspection graphs. [Reproduction](lean/repro/GroupedSpine.hs); `SupportSpineAlternatives`. |
| 9 | Sparse nested substitution could discharge a guard that complete evaluation rejected, admitting an invalid term. | Retain the guard and return `SolverUnknown` for the reproduced enclosing-name conflict. Safe flat ambiguous scopes can compile. This does not assert an empty language. [Pruning reproduction](lean/repro/NestedScopeCapture.hs), [compiler reproduction](lean/repro/NestedCompileCapture.hs); `PruneAmbiguity`, `SourceEnclosingRenames`. |
| 10 | Equivalent conjunctions grew from size 9 to 29 to 89 during repeated acyclic equality reduction. | Flatten outer conjunctions, remove `Top`, sort, and deduplicate while preserving scopes. The retained case stabilizes. [Reproduction](lean/repro/PruneConjunction.hs); `GuardConjunction`. |
| 11 | Combining independently interpreted guards could change an operand's meaning and admit a term rejected by an input automaton. | Allocate each outer Boolean operand independently and preserve nonempty substitution scopes. The reproduction now reports `[Yes, No, No]`. [Reproduction](lean/repro/ConjoinScope.hs); `SourceBooleanEntry`. |
| 12 | Recursive equality narrowing repeatedly expanded equivalent domains and exceeded the retained runtime limit. | Block constrained recursion while retaining the original equality constraint. The current binder constructor also removes its bare self-reference from root unions. [Reproduction](lean/repro/RecursiveReduction.hs); `ConstrainedRecursionGate`, `BinderSelfUnion`. General nontermination of the old example was not proved. |
| 13 | Observing an imported explicit union could drop every valid term and report `EmptyGenerator`. | Expose `InternedUnion` through the finite epsilon closure before ordinary observation splitting. [Reproduction](lean/repro/ImportUnion.hs); `ImportObservations`. |
| 14 | Observation filtering could reject valid recursive groups as `UnboundedGenerator` and lose their size indexes. | Filter the ascending key map directly and retain complete recursive records. [Reproduction](lean/repro/RecursiveGroupFilter.hs); `RecursiveGroupFilter`. |
| 15 | `boundDepth` could loop on retained empty binder cycles even though their outer-edge closure was empty. | Use visited `nodeEdges` exposure uniformly before recursing into constructor children. [Reproduction](lean/repro/BoundRetainedBinders.hs); `LexicalBinderClosure`. |
| 16 | A syntactic extraction such as `v == v` could be treated as an exact integer measure and remove valid expressions. | Reject fallback measures that depend on the refined value. Preserve exact singleton extraction priority. [Reproduction](lean/repro/SelfDependentMeasure.hs); `DefiningTerm`, `ParentGuardFormula`. |
| 17 | Recursive open group positioning queried cardinalities, built an empty position map, and raised `Map.!`. | Read the available group keys directly. Unsupported recursive integer closure now returns its existing explicit error. [Reproduction](lean/repro/RecursiveOpenPositions.hs); `GroupPositions`. |
| 18 | In one substitution scope, merging equal actual identities could remove the first identity replacement and expose a later replacement for the same formal. Sparse evaluation returned `Yes`, pruning admitted a rejected term, and compilation produced one invalid tuple. | Return `Unknown` when an uncertain identity replacement has a later non-identity replacement for the same formal. Later literal identities remain accepted; allocator coherence proves this refinement safe. Pruning retains the guard; compilation returns `SolverUnknown`. The existing [guard/pruning reproduction](lean/repro/NestedScopeCapture.hs) and [compiler reproduction](lean/repro/NestedCompileCapture.hs) now check both nested and same-scope cases. `SameScopeIdentityCapture` retains the pre-repair witness; `SourceSubstitutionPrecedence` proves the new check. |
| 19 | A recursive callback could inspect temporary support and select different bodies during count, term, and support rebuilds. The public bounded generator returned four terms that its support rejected. | Keep construction tokens separate from size flags. Reject payload queries until the definition completes. Nested definitions retain enclosing tokens; both recursive and finite return paths remove their own token. `RecursiveConstructionQueries` proves marker provenance, stable rejection, and completed query behavior. The existing recursive-member case in `GenSpec.hs` checks the original callback, fourteen query paths, and nested-family completion. See [the construction-query notes](lean/notes-recursive-construction-queries.md). |
| 20 | Grouped key discovery retained an earlier minimum after a callback changed its base. `minimumSize` returned zero although counts were `[0,1,1,1]` and the smallest member had size one. | Compare the final probe's keys and minima with the accumulated discovery table. Return `InconsistentRecursiveFamily` on disagreement. `GroupedProbeValidation` derives a true body fixed point for every successful check and proves that constructor programs retain their previous least-attained minima. The existing recursive-member test retains the public callback. See [the discovery-validation notes](lean/notes-grouped-probe-validation.md). |
| 21 | `mergeAlternatives` on the union of two recursive languages repeatedly unfolded the same child union. Direct recursive operands and wrapped union operands exceeded the diagnostic timeout. | Stop recursive merging at retained recursive or union boundaries. Preserve the union and its accepted terms. The direct merge and enclosing equality reduction now complete. [Reproduction](lean/repro/MergedNarrowing.hs); [proof boundaries](lean/notes-merged-narrowing.md). |
| 22 | The retained recursive child union was immediately unfolded into an ordinary node. Repeated equality passes on five recursive alternatives added six nodes and sixteen edges per observed pass. Public pruning exceeded the diagnostic timeout. | Use `createUnion` at the recursive-boundary return to retain the explicit union. The same public prune call completes. The retained fixture has idempotent merging and reaches an equality fixed point after two changing passes. This finite evidence does not prove general nested-schedule termination. See [merged narrowing notes](lean/notes-merged-narrowing.md) and [the source reproduction](lean/repro/MergedNarrowing.hs). |
| 23 | A closed structural constructor program aliases a live ordinary capture and reaches a pending Mu pair. Both native translations exceed five seconds at root evaluation. | Select a placeholder above the Depth observation's free ordinary levels and reuse that choice in `matchMu`. The kernel checks the old pending slot and repaired completion. All five native probes and 620 examples pass. General repaired completion remains open. See [closed pending](lean/notes-paired-pending-boundary.md) and [repair proofs](lean/notes-fresh-ordinary-candidate.md). |

The private `Recursion` repair changes engine-term shape. User values,
surface terms, original generator counts, distributions, and rank order
retain their semantics. Importing raw support counts the new private nodes
as nodes, so an imported node-count bound can change.

## Rebase integration and optimization coverage

The new upstream equality worker performs one pass. Its proof now describes
that operation directly. Explicit pruning and partial-reduction callers still
use fixed points where the source does. The formalization no longer attributes
an internal fixed-point loop to the public one-pass worker.

The classified similarity optimization preserves the exact ordered eligible
pair list and inference-error behavior. Its candidate comparison count is
the sum of `n * (n-1) / 2` over the classes. Classification, maps, and solver
costs remain separate. See [the similarity proof notes](lean/notes-similarity-within.md).

The indexed minimizer preserves the previous full-table schedule, including
root representatives and final copy passes. Installing a root representative
creates child links. The rebase integration now adds those parent-index
entries. Otherwise a later indexed copy could miss an inserted edge.
`MinimizeParentIndex` proves complete schedule equivalence and the required
metadata invariant. This is an integration obligation; it is not counted as
a separately reproduced public defect. See
[the parent-index notes](lean/notes-minimize-parent-index.md).

Retained size masses also move when constructors pay a size unit. Earlier
integration omitted those shifts in two paths. The source and transport
proofs now preserve the member/mass alignment.

The constructor record model omitted the current root self-reference filter.
`compileBody` now applies it at both probes and at the reserved binder identity.
The coherence, pending-record, and replay proofs include that reconstruction.
Kernel checks show that a recursive body with an added bare self operand
returns the same canonical record as the body without it. A second check
covers cleanup to an ordinary node. This repairs a source-correspondence
omission in the formalization; it is not a new Haskell defect. The lexical
`InternedBinderRebuild` and full `InternedSubstitution` worker now apply the
same filter. Their capture-avoidance, exact-language, free-reference, and
finite-allocation results remain proved.

## Recursive construction query repair

The pre-repair reproduction uses only public operations:

```haskell
recur $ \self -> case support self of
  Right EmptyNode -> oneof [pure 0, node "step" ((+ 1) <$> self)]
  _ -> leaf 99 "wrong"
```

Before the repair, the bound-three generator had four ranks and values zero through three,
each with probability one quarter. Its support rejects all four returned
engine terms. Count, sampling, and term rebuilds expose EmptyNode through
the placeholder; support reconstruction exposes its live recursive node.
The original public guardedness test accepts the body. The public API does
not state that a builder must avoid inspecting its argument.

The repair makes `support self` return `QueriedRecursiveOccurrence` in every
rebuild. The callback consistently returns the finite value 99. Its term
belongs to the returned support. Independent construction tokens remain
present during closed probes, which deliberately clear size-index flags.
The reproduction and pre-repair output are `/tmp/mcfta-context-builder.hs`
and `/tmp/mcfta-context-builder.log`; the repaired result is in
`/tmp/mcfta-context-builder-repaired.log`. The existing suite retains the
callback and the nested selected-key completion case.

This repairs the observed payload-query mismatch. It does not establish
regularity of every arbitrary callback or monotonicity of key discovery.
An empty family has no active records to reject. A callback can observe that
initial state and change its finite base after keys appear. Row 20 validates
the final discovered table before the source returns a tied family.

## Behavior that does not satisfy the stronger requested contract

**Similarity minimization preserves representatives, not every original
term.** Repairing root deletion does not make it an exact-language
optimization. A caller that requires all original expressions must not use
the representative theorem as a completeness theorem for the original set.

**Pool minimization does not preserve similarity-class probability.** It
starts a uniform distribution over the retained entries. The checked example
changes class masses from `2/3, 1/3` to `1/2, 1/2`. No discarded weight is
transferred to a representative. See
[the probability notes](lean/notes-pool-minimization.md) and
[the public reproduction](lean/repro/MinimizedPoolDistribution.hs).

**Unsupported or uncertain constraints are not empty languages.** General
quantified and nonlinear constraints lack a complete terminating solver
contract. The lattice backend rejects unsupported syntax, including `Ite`.
`Unknown`, timeout, unboundedness, and missing inspection fields remain
explicit states or errors.

**Logical alpha-equivalence does not imply identical solver verdicts.** A
sound name-sensitive callback can change `Yes` to `Unknown`. The supplied
adapter also rejects a generated actual name that collides with an unused
ambient declaration. No invalid term is admitted by that example. Exact
verdict preservation needs a name-transport/freshness contract. See
[the boundary notes](lean/notes-guard-alpha-boundary.md).

## Verified model coverage

The checked development includes independent constrained grammar derivation,
FTA acceptance, finite-term enumeration, exact finite distinct-term ranks,
symbolic count/select/rank workers with caches, supported lattice counting
and ranking, and exact rational distributions. It also covers the stated
intersection, pruning, canonical guard, minimization, and interning algorithms.
Their scope and premises are recorded in [SYSTEM](lean/SYSTEM.md),
[COVERAGE](lean/COVERAGE.md), and [API-COVERAGE](lean/API-COVERAGE.md).

The latest committed recursive work connects independent value and term
indexes, source count and sampler equations, complete inverse queries,
candidate flags, ordering, distinct returned positions, and bounded global
ranks. It includes arbitrary-branch single-root bodies and binary-choice
mutual key families. `GroupedMergeAssociativity` preserves the complete
ordered member and rank-probability fields under regrouping.

The aggregate audit now includes those results for arbitrary-branch mutual
families. The new dispatch proof distinguishes bare
singleton grouped merges from raw singleton choices that add `Choice 0`.
The original typed guard proof distinguishes a user label from a plain pay.
Both add size; only the label supplies the corresponding term-growth guard.
See [the n-ary notes](lean/notes-keyed-nary.md) and
[guard notes](lean/notes-keyed-nary-guards.md).

The recursive-join adapter now composes the actual `JoinN`, `CenterKeyed`,
and `ArgKeyed` structures through typed nested joins and mutual families.
It preserves heterogeneous argument values, aligned term ranks, retained
masses, and complete ranked samplers. The record-to-selector bridge is
complete. Mutual callback induction and the public replay filter establish
all-view and bounded global decoder preimages. Original occurrence metadata
supplies the public guards. Candidate bounds include false flags. Callback
and public rank lists are ordered and have no duplicate positions under
their local finite-leaf contracts. Ordinary `Apply` remains a separate constructor.
Support, diagnostic inspection, both sampling routes, weight flags, and
absent-term branches now have constructor-derived adapters.
`RecursiveCompleteRecord` ties these fields and the original occurrence
checks to one checked program. Arbitrary runtime schema changes remain open. See
[the join notes](lean/notes-recursive-join-fields.md).

## Evidence and its limits

- Latest source suites: **620 passing examples**, on `9508eb3` plus local
  repairs `558b316` and `e0e1b37`. Log: `/tmp/mcfta-fresh-probe-620-tests.log`.
  Fourmolu and Cabal-gild checks pass. Both retained recursive-merge source
  cases and both ordered-profile/rank-stutter source replays also pass.
- Repaired nested and same-scope source probes both report `(No,Unknown)`
  for complete/sparse evaluation, `(No,No)` before/after pruning, and
  `Right []` versus compiler `Left SolverUnknown`.
  Log: `/tmp/mcfta-scope-precedence-repaired.log`.
- Latest integrated Lean audit: **1,026 jobs; 36,839 theorem dependency checks**.
  Only `propext`,
  `Classical.choice`, and `Quot.sound` are allowed.
  Log: `/tmp/mcfta-20261013-final-restart-audit.log`.
- The earlier formula capture, nested compiler capture, recursive equality,
  and open-union reproductions passed at the `de910ea` checkpoint. The independent two-key
  recurrence again checks all eight classes and 285 inverse ranks, including
  exact masses, conditional probabilities, and support acceptance.
  Log: `/tmp/mcfta-de910ea-focused.log`.
- Independent source probes covered 5,000 finite grammars; 1,536 mixed
  grouping/recursion descriptions; nine automaton-import variants; 144
  weighted descriptions across nine size bounds; and 2,080 bounded recursive
  intersection comparisons.
- The new heterogeneous `Bool`/expression join recurrence checks eight
  classes and 37 member inverses, exact masses, and support acceptance.
  Log: `/tmp/mcfta-heterogeneous-join-replay.log`.
- Earlier exact-rational recurrences checked 132 single-root and 254 two-key
  member inverses. The 285-rank delayed-third-branch probe was rerun above.
- Shared equality FTAs with `2^60` and `2^80` distinct terms passed exact
  counting and distant decode/rank round trips without enumerating their
  language. These are feasibility checks, not general benchmarks.

Efficiency has separate proof obligations. Balanced selection has checked
comparison/query bounds. Symbolic selection skips counted blocks, while
overlap preprocessing can be exponential. Polynomial evaluation and
arbitrary-precision arithmetic are not free. `groupBuilt` still enumerates
an already-built finite source during observation compilation.

The Lean sources are handwritten models and algorithm ports. The audit
checks their logical dependencies; it does not verify Haskell-to-Lean
translation. Source reproductions and finite probes support correspondence
but do not prove it for every runtime execution.

## Detailed component results and remaining obligations

The current proof checkpoint is **`073c10c`**. The integrated working audit passes
**1,026 jobs and 36,839 theorem dependency checks**. Stable proof modules
are committed and imported by the working aggregate audit. The full
formalization remains incomplete. The detailed restart order, commands,
repository safeguards, and supporting file map are in [HANDOFF.md](HANDOFF.md).

### Full nested source profiles and exact stored body tags

`InternedNestedProfiles` proves root-profile correspondence and the decoded
Mu-profile heap invariant for arbitrary full constructor `Syntax`. It covers
actual ordinary constructors, root self filtering, both probes, fresh-body
execution, smart/raw cleanup, canonical cache hits, and pending outcomes.
There is no binder-free restriction or assumed callback equation. Profiles
retain opacity and the set of literal root references. They do not retain
ordinary structure, Mu identities, or canonical union order.

`InternedStoredMuOrigins`, `InternedNestedMuOrigins`, and
`InternedProfileMuOrigins` derive the actual original source expression,
captured environment, three normalized calls, reservation, and historical
invariants for every completed stored Mu. The enclosing execution may itself
stop at another pending key.

`InternedStoredProbeTags` then proves:

- A stored body is EmptyNode exactly when both probes are EmptyNode.
- A stored body is its own reserved reference exactly when the probes are
  `RecDepth` and `RecUnint 0`.
- Smart cleanup returns EmptyNode exactly in those two key cases.

These are source-derived statements about all stored records, not finite
sample conclusions. See [the source profile notes](lean/notes-interned-root-profile-source.md),
[verified origins](lean/notes-interned-profile-reflection.md), and the dated
03:21/03:28 results in [the gate notes](lean/notes-gate-unfolding-rank.md).

### Preserved baseline constructor results

These modules describe the preserved old executor. Its general completion
claim is now refuted by the closed pending example in row 23. The repaired
executor has separate semantic heaps and still needs a general completion proof.

`InternedSpecialKeyCompletion.closed_safe` excludes pending readback at
`(Empty, Empty)` and `(Depth, Unint 0)` for **unrestricted closed Syntax**.
It has no admission grammar, callback-law, or whole-run-success premise.
The proof obtains earlier completed nested sites from the actual depth-body
trace. `InternedProfileReferenceInputs` derives the required invariance under
arbitrary literal-reference aliases.

`InternedPendingProfileBoundary.closed_remaining` restricts any remaining
hypothetical encounter to two opaque probes, or two pure probes with nonempty
fixed captured root references. `InternedPendingOldCall` independently retains
the active fresh ancestor reference and both exact probe records already
available before that ancestor reservation.

Exact local replay now covers ordinary nodes, unions, root filtering, and
cleanup through actual common cache extensions. `InternedBoundaryFreeAge`
includes free names inside old boundary Mu payloads. `InternedLiteralObservations`
derives empty-result agreement and forward bare-local reflection for actual
full-Syntax calls with arbitrary same-length literal aliases. The remaining
step is the dynamic Mu boundary/identity argument. Set equality of root
profiles cannot establish exact canonical request replay. `InternedProbeFreeSupport`
propagates free-name absence through stored probe dependencies.
`InternedProbeDependencyAge` proves strict identity descent and well-foundedness
for that graph. This is not a body-unfolding rank. `InternedOldProbeReplay`
closes the old complete-record hit case from its two smaller probe observations;
the newer smart-Mu case still needs joint boundary transport.

**Full free-name semantics and its source heap invariant are proved.**
`InternedFreeNameSemantics` covers all Syntax, with arbitrary external-name
maps. `InternedFreeNameForm` derives fixed captures and an optional argument,
including captured probe aliases. `InternedNestedFreeNames.build_free` and
`closed_heap` follow the actual mutual source execution, including cache hits,
fresh body calls, and pending outcomes. `InternedSourceFreeNames.closed_free_empty`
proves that every completed closed run has no free names.

`InternedFreeNameMuOrigins` retains both semantic tables at each stored Mu's
historical source prefix. `InternedStoredFreeNameBoundary.closed_reference_absent`
uses those origins: an old-free-name bound on the actual stored body excludes
fresh literal boundaries in both original probes. The fresh Mu-boundary half
remains open. See [the free-name proof](lean/notes-interned-free-names.md).

`InternedPureProfileIdentity.ordered_identity` identifies available pure values
from equal ordered profiles in a common normalized state. Its checked reverse
union example disproves identity from set equality. The checked warm-cache
example in `InternedPureProfileOrderBoundary` disproves exact ordered syntax
correspondence. The next proof must derive actual ordered replay; it cannot
replace profile equivalence by ordered equality.
See [the special-key proof](lean/notes-interned-special-key-completion.md),
[observed root replay](lean/notes-interned-observed-root-replay.md),
[boundary transport](lean/notes-interned-boundary-transport.md), and
[literal observations](lean/notes-interned-literal-observations.md).

### Live lexical replay and actual probe sites

`InternedFreeAbsenceReplay` proves exact raw source replay after an interned
free name disappears. `InternedLiveInputReplay` strengthens this to arbitrary
literal maps that agree at the pure interpreter's live lexical positions.
`InternedLiveInputReadiness` excludes a later pending request from an earlier
completed matching site and the later actual completed probes. It does not
assume the later binder completes.

`InternedProbeChoiceSites` extracts actual earlier sites along chosen Depth
or Unint callbacks. Each crossing retains its computed ordinary level and
chronological cache-growth evidence. `InternedLiveInputSupport` derives the
needed agreement when every changed current input is fresh and the current
probe is an older available record. General encountered scopes can also
have different Unint levels. Those differences remain an explicit gap.

`InternedProbeChoiceSites.completed_route` now retains the exact source body
at every crossing, as well as its probe choice and cache history. This
supports comparison with the actual pending descendant path. Do not assume
that a stored body's depth equals either probe's depth:
`InternedClosedProbeCostBoundary.actual_depths` checks depths `(1, 0, 0)`
in a record created by a closed source run. This is a boundary for the
proposed invariant, not a source divergence counterexample.

`InternedPendingOrdinaryMismatch.closed_depth_mismatch` now derives two
completed Depth calls of the same source body with different cached depths
from any hypothetical closed pending run. It derives the active source
origin, both lexical routes, literal contexts, and chronological histories.
No assumed callback equality or externally supplied origin is required.
The remaining ordinary-level mismatch case is not yet excluded.

### Physical comparison and cold execution

`MergedOrdinaryHeight` and `MergedMergeTermination` give a decreasing measure
for guarded recursive merge calls. `MergedComparisonSource` includes the
source EmptyNode shortcuts and ordered arity checks. `MergedPhysicalWarmup`
and `MergedPhysicalComparison` derive a finite physical inventory for the
`PreparedWithoutMu` fragment. `MergedPhysicalLanguage` proves exact finite
term semantics for its epsilon reader. `MergedPhysicalUnion` proves exact
operand-union language through actual normalization and cache readback.

`MergedColdExecution` and `MergedColdInventory` derive completion per unfold,
finite cache changes, and a finite inventory for one generated chronological
trace. They require no eager warmup and do not compare hypothetical allocation
histories. `MergedColdReaderFacts.read_closed` now proves successful ordered
source edge exposure for closed roots in that fragment. It returns resident
edges with closed children, the exact final cache, preserved facts, and exact
stability under extra proof fuel. `MergedSourceExposureLanguage` derives
actual epsilon origins for every returned edge and proves finite-term
soundness. `MergedSourceExposureCoverage.actual_exact` now supplies reverse
coverage and exact language in the actual returned cache. The full ordered
stateful comparator completes with exact fuel stability and later replay.
Its actual-cache semantic inclusion and exact child-selection language are
proved. Full cold merge composition remains active.

`MergedPhysicalGroupRoot.grouped_root_covers` proves ordinary-root language
coverage through actual child, edge, and parent effects. The checked column
worker derives filtering soundness from physical comparison and covers
singleton, retained recursive union, and ordinary union branches. Recursive
certificates apply only below the parent height. The later `MergedAdaptiveMerge.execute_complete` composes those
certificates with current-state selection and derives the complete prepared
worker result. Its remaining source correspondence boundaries are explicit.
See [physical comparison](lean/notes-merged-physical-comparison.md),
[actual union semantics](lean/notes-merged-physical-union.md), and
[cold execution](lean/notes-merged-cold-comparison.md). The new
[cold reader](lean/notes-merged-cold-reader.md) and
[physical group](lean/notes-merged-physical-groups.md) notes give exact scopes.

### Equality fixed-point termination

**Source baseline change:** PR #97 inserts `mergeAlternatives` after every
peer projection. The original `EqualityLeafProjectionRuntimeBound` still
models the previous worker. The new `MergedProjectionBound.compiled_bound`
now proves the complete merged projected-leaf schedule. It covers physical
row grouping, exact source edge and node requests, snapshot targets,
simultaneous edits, class order, required paths, and the final fixed point.
`MergedRawLeafSource.worker_actual` uses the actual runtime output cache;
no later operation executes from a proof-prepared cache. Group iteration
order is explicit and must include all source symbols. The bound remains
the original occurrence weight plus one. Endpoint domains must be leaves.

`MergedAlternativesSubsumption` proves soundness of successful bounded
recursive coverage checks, including ancestor-pair reuse. `MergedEqualityReduction`
proves full constrained-language preservation under a merge-superset contract.
The physical leaf worker now has a language-coverage theorem. Complete
group orders give equal records in a common cache, and an observed row order
derives completeness. Coverage search saturates under a complete finite pair
inventory. General recursive merge termination and the recursive physical
superset bridge remain open. See [merged narrowing](lean/notes-merged-narrowing.md).

The complete physical **projected-leaf** schedule has a derived bound of the
original occurrence weight plus one. It includes actual endpoint reads,
first-seeded target folds, recursive ancestor edits, required paths, class
order, empty propagation, and an allocation-free final fixed point in the
actual runtime cache. Endpoint domains must be leaves; ancestors may be nested.
Raw guard normalization and rejected constructor allocations are included.

Two source-correspondence gaps were repaired in the formalization. Raw leaf
pullback and dead-row trimming prevent proof-prepared caches from becoming
runtime inputs. The physical intersection model now includes the source's
ordinary-node identity orientation. The path worker uses the exact ordinary
source union branch. These were model repairs, not additional Haskell defects.
The 4,096 projected forests and 1,156 raw leaf source pairs pass again. See
[the runtime bound](lean/notes-equality-leaf-runtime-bound.md) and
[runtime trimming](lean/notes-equality-leaf-runtime-trim.md).

For one fixed **binary projected class**, `EqualityFixedProjectionInvariant`
proves that every original occurrence retains its rows after the first
reciprocal pass. `EqualityFixedProjectionTermination.run_bounded` counts missing
occurrence-row pairs in a finite complete inventory. Nested endpoint rows are
allowed. Its premises include a static commutative row relation with admitted
diagonals. The physical adapter, disappearing-ancestor phase, raw normalization,
and interaction with other classes still need composition. A public Haskell
probe with nested endpoints takes four changing passes and agrees with this
invariant. See [the binary-class proof](lean/notes-equality-projected-binary.md).

The general nested fixed schedule remains open. New checked obstructions are:

- `EqualityFixedMultiplePeers`: a convergent three-peer source-shaped example
  removes a row after the first pass. Binary occurrence growth does not extend
  directly to larger classes. Its separate abstract Steiner cycle shows that
  commutativity/idempotence alone are insufficient; it is not a source cycle.
- `EqualityFixedDegreeCounterexample`: the five-degree source leaf table has a
  nonassociative mutually reachable narrowing component. Public Haskell confirms
  the table and witness. Such components cannot be assumed to be semilattices.
- Earlier `EqualityFixedSaturationCounterexample`: alternating targets can
  return to an earlier representation even with the same recursive closure
  image. An arbitrary-target rank is unavailable.

`EqualityFixedRowProfile` derives local Boolean row behavior when higher
profiles agree. `EqualityFixedProfileMaximum` proves a removable maximum for
one finite powerset layer over a strict-ranked row base. These results do not
supply arbitrary nested lifting. Synchronized higher-profile induction is a
candidate next route. No cycle of the actual fixed source schedule is proved.

### Recursive gate rank: pure probes complete, opaque probes remain

`InternedPureProbeGate` and `InternedProbeOpacity` derive actual stored-body
unfolding completion and strict head-rank decrease from a pure depth probe.
The second probe is also pure, its level is zero, and the actual body depth is
zero. The original source syntax may have arbitrary nesting. Earlier shallow,
reachable-only, closed-nested, and marker one-step results retain their scopes.
The general case with **opaque probes** remains open.

The following checked examples rule out attempted generalizations:

- `InternedOldBodyProbeAliases`: a smart unused old body can differ from both
  normalized probes because captured sentinels are filtered differently.
- `InternedNestedProbeCostBoundary` and `InternedClosedProbeCostBoundary`:
  exact free-occurrence cost coverage fails in a completed closed source-model
  cache at slot 19. The body has external sentinel costs 1; both probes have
  those names only at cost 0. The closed program returns EmptyNode. The existing
  `FlatProbeHeap` theorem must retain its restricted scope. Haskell confirms the
  open fixture and both actual-own-to-probe substitution equations.
- `InternedSourceRankStutter`: staged scoped source-model construction with
  explicit `Depth`/`Unint 2` captures and cache prepopulation gives an actual
  modeled unfolding where both head rank and free-occurrence rank stay at 2.
  The continuation has ranks `[2,2,1,0]`. This does not establish divergence,
  closed empty-environment reachability, or universal callback admissibility.
  Haskell now confirms both rank traces and the preloaded representative. The fixture fails the unrestricted callback renaming law when the old name aliases its fixed capture. See [the source replay](lean/notes-source-rank-stutter-replay.md).
- Exact ordered root-profile correspondence is false. Reversing captured union
  operands can hit the same Mu key and return the first stored order. The
  temporary kernel check `/tmp/mcfta-profile-order.lean` passes after completing
  its inequality proof. The set-based `Equivalent` theorem remains valid.

These are proof-obligation counterexamples. They do not add production defect
rows to the repaired defects above. See
[the gate notes](lean/notes-gate-unfolding-rank.md) and
[literal profile order](lean/notes-interned-literal-observations.md).

### Other remaining source contracts

Typed nested-join families now connect support, diagnostics, both sampling
routes, weights, flags, complete inverse queries, and original occurrence
metadata. `RecursiveCompleteRecord` assembles those fields. Arbitrary opaque
Haskell builder schemas, key-discovery behavior, codecs, and lazy productivity
still require their stated contracts. Generator members remain distinct from
unique accepted FTA terms.

Full sparse Yes transports to complete logical satisfaction. Current pruning
and successful compiler classification inherit logical safety and exactness on
the success domain. A sound name-sensitive backend can still return sparse Yes
and complete Unknown. Exact backend-confirmed language equality requires
backend adequacy. The all-Int adapter derives its laws from correctly returned
external responses. See [logical read transport](lean/notes-source-read-logical.md)
and [the integer adapter](lean/notes-source-read-integer-adapter.md).

Runtime identity lifetimes, machine words, host containers, concurrency, lazy
productivity, solver IO, PRNGs, and user codecs retain explicit correspondence
contracts. There is no verified Haskell-to-Lean extraction. Similarity
minimization preserves representatives, and pool minimization starts a new
uniform distribution; neither implies exact term/mass preservation under the
stronger requested contract.

These boundaries prevent a whole-implementation verification claim. Resume
from [HANDOFF.md](HANDOFF.md), using [NEXT-PROMPT.md](NEXT-PROMPT.md). Keep the
proof checkpoint, source fixes, and all restart material local.
