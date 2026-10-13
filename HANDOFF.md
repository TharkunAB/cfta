# microcfta formalization restart handoff

Updated: **2026-10-13 15:06 CEST (Europe/Stockholm)**.

## Read first

The formalization is **not complete**. Matti requested this restart checkpoint
because the chat became unreliable. Continue the same full task. Do not replace
it with a smaller fragment, a theorem-count target, or a documentation task.
The latest committed proof checkpoint is **`22d0adc`**. The integrated working
audit passes **919 jobs; 34,817 theorem dependency checks**. New proofs give
ordered stateful comparison completion, exact fuel stability and replay,
exact cold-reader semantics in the returned cache, adaptive fuel independence,
cold child-selection completion and exact language, derived source grouping,
and actual ordinary-capture origins for any hypothetical closed pending run.
Comparison soundness now holds in its actual returned cache.
The new source repair is `c76d1ec`. Inspect the live working tree before
proceeding; more proofs can be in progress. Preserve every current result.

Read this file, root `FINDINGS.md`, and the linked notes before new proof work.
Root `FINDINGS.md` is the current report. `lean/FINDINGS.md` is historical.
Dated sections in detailed notes describe successive checkpoints; later results
can discharge an earlier section's stated gap. Use the theorem statements and
this handoff for current scope. `NEXT-PROMPT.md` contains the restart prompt.

## Immediate restart state and targets

This continuation has active proof work. Inspect the current working tree and
workers before resuming. All stable Lean modules are imported by the working
`MicroCFTA/Audit.lean`. The original marked draft
`lean/MicroCFTA/MergedAdaptiveStability.lean.incomplete` remains committed and
excluded from build targets. Its completed sibling now proves the requested
fuel independence. Preserve the marked draft unchanged.

At this restart, `git pull --ff-only origin microcfta` refreshed the source
branch and reported already up to date. The fetched remote remains
`489783177b0a7fd34bb6bf205e66d7d5cce0d1fe`.
`git rebase origin/microcfta` then reported the continuation branch up to date.
There were no newer commits to replay. Backup
`backup/formalization-before-refresh-20261013-1435` retains `efd0ddc` and
every prior proof, counterexample, and the marked draft. The Lean tree was
unchanged by the refresh. Existing stashes and other worktrees were untouched.
Fetch again at restart because more patches can arrive later.

Latest full validation: **919 jobs; 34,817 theorem dependency checks**.
Log: `/tmp/mcfta-20261013-sound-selection-audit.log`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
The latest source tests remain **620 passing examples** at source repair
`c76d1ec`; no Haskell source changed after that repair.

Latest proof checkpoints:

| Commit | Result |
| --- | --- |
| `47ca7f0` | Physical group, edge, column, and parent construction coverage. |
| `6d3a7d6` | Ordered cold edge reader succeeds for closed prepared roots. |
| `67d942b` | Closed stored body/probe depths can be `(1,0,0)`. |
| `8dd0761` | Completed probe routes retain exact source bodies and histories. |
| `26cbcfc` | Closed pending execution requires an actual ordinary-level mismatch. |
| `fee28ff` | Cold reader edges have actual epsilon origins and finite-term soundness. |
| `a15bde6` | Fresh-only captures can change an actual computed ordinary level. |
| `40034d8` | Complete adaptive physical merge terminates and covers its input language. |
| `2ba84e1` | Ordered comparison effects, cold progress, and exact reader replay. |
| `b0849b3` | Exact adaptive merge fuel independence; marked draft preserved. |
| `321e401` | Ordered stateful comparison completion and fuel stability. |
| `c14eac9` | Live ordinary capture required by closed pending construction. |
| `fd18cb9` | Exact cold-reader coverage in the actual returned cache. |
| `666ab5d` | Exact ordered comparison replay after cache growth. |
| `19b0dad` | Stable ordered cold child-selection completion. |
| `29443f3` | Stateful comparison soundness in its actual returned cache. |
| `77c717f` | Exact actual-cache language of cold child selection. |
| `f9fe9f3` | Earlier ordinary-capture source calls and a checked alias boundary. |
| `22d0adc` | Derived exact full-key grouping and source bucket equations. |

Use the following proof order. These are concrete next obligations, not a
replacement for the full objective.

1. **Ordered comparison is available for composition.** Completion and stability are
   proved in `MergedComparisonCompletion` and `MergedComparisonStability`.
   The bound uses cold original Mu records and unvisited issued identity
   pairs. `MergedComparisonReplay.check_replay` preserves every successful
   Boolean in a later cache without effects. `check_observation` derives a
   prepared common observation. `MergedComparisonSoundness.check_sound`
   now proves inclusion for successful true results in the actual returned
   cache, without `Ready` or warmup. Finite-term induction and coherent
   numeric identity justify ancestor reuse. Keep failed-cover effects and
   short-circuit order in the merge composition. Read `lean/notes-source-comparison-handoff.md` and
   `lean/notes-source-comparison-soundness.md`.
2. **Cold source selection and merge composition.**
   `MergedSourceSelection.select_complete` derives a stable exact retained
   list and cache without warmup or a recursive comparison premise. It
   preserves facts and all original records. `select_complete_exact` also
   proves exact union language in that returned cache. `recursive_member`
   checks the source's identity-membership shortcut. Connect this ordered
   filter to the complete cold merge worker. The existing adaptive
   worker has derived completion, language coverage, and fuel independence.
   Initial prepared `Context`, concrete guards, structural `Grouping`, and
   outer memoization remain correspondence boundaries. Concrete grouping now
   has `MergedSourceGrouping.groups_correct`; source bucket order has an
   exact append-fold equation. Read
   `lean/notes-merged-adaptive-worker.md`.
3. **Exact reader semantics are now available.**
   `MergedSourceExposureCoverage.actual_exact` proves edge membership iff
   epsilon origin and exact finite-term semantics in the original returned
   cache. `nodeEdges_exact` extends this to later caches with source facts,
   preparation, and availability. No global `Ready` or warmup is required.
   Use these results in comparison and cold merge proofs.
4. **General closed constructor no-pending.** Read
   `lean/notes-interned-literal-observations.md`.
   `InternedPendingLiveMismatch.closed_live_depth_mismatch` derives same-body
   completed Depth calls with different depths at a live lexical position.
   The later ordinary name occurs in the old Depth probe and is a live
   capture of the active ancestor. It occurs in the old ordinary probe too
   unless it equals that probe's supplied local.
   `InternedPendingOrdinaryOrigins.closed_capture_depth_mismatch` derives the
   actual earlier introducing callback with fewer lexical inputs. The
   new `InternedOrdinaryCaptureBoundary` closed example completes while
   realizing levels `(0,1)` and the later name in the old Depth probe.
   Support or alias alone is not a contradiction. Retain both exact pending
   key components and derive a mismatch in the shorter producer context.
   General equal-depth transport is
   false: `InternedOrdinaryLevelBoundary.different_actual_levels` checks
   captures `[Depth,Depth,U0]` versus `[interned 9,Depth,U0]`, with depths 0
   and 1. Its closed embedding stores nested depths `(1,0,1)` at slot 28 and
   completes with an empty root. This is not a pending counterexample.

The source preparation restriction remains `PreparedWithoutMu` for every
complete Mu body. It permits closed nested Mu records of arbitrary depth.
It excludes reconstruction through open nested Mu records. Full arbitrary Mu
totality, general nested equality fixed-point termination, concrete runtime
correspondence, and the other contracts below remain part of the objective.

Temporary diagnostics are useful but are not durable proof prerequisites.
The fixture-guided mirror checked 14,916 variants, skipped seven for resource
limits, observed 12,903 level-changing traces, and found no pending readback.
Files: `/tmp/mcfta-pending-level-search.py` and its `.log`.
The checked fixtures and exact statements are committed in Lean.
The local weekly monitor last reported **84% remaining**. Refresh
it at restart; stop all work at 1% or less. Do not rely on this snapshot.

## Full objective and authorization

The persistent user objective is:

> Keep going until you finish the formalization. Work around any issues you
> encounter, and note your fixes in FINDINGS.md.

The required properties remain:

1. Compile constrained languages to exactly their valid finite terms.
2. Prove enumeration sound and complete. Exact optimizations must retain all
   required terms and their weights.
3. Give every distinct accepted FTA term one rank and prove both inverse laws.
   Generator member multiplicity is a separate contract.
4. Prove requested probabilities. State algorithmic costs separately from a
   materialized reference enumeration.
5. Compare executable Lean definitions with the current Haskell implementation.
   State representation and external contracts explicitly.

**Usage stop:** Matti instructed: "If the usage reaches 1% or less, you
should stop (so we don't use credits)". This means weekly allowance remaining.
Check current account rate-limit reports regularly. Stop all workers and work
at 1% remaining or less. `/tmp/mcfta-weekly-usage.py` prints the latest local
weekly report and exits 99 at the threshold. Do not treat missing or stale
usage data as permission to spend credits.

Local proof work, focused source diagnostics, and necessary source repairs are
authorized. **Keep new work local. Do not push, deploy, or post to the board.**
Matti later authorized one push to `formalization/microcfta`. Checkpoint
`8a80947` was pushed and independently verified there at 04:33 CEST.
That completed request does not authorize publication of new work. The prepared board
payload `/tmp/mcfta-board-proposed.json` must remain local.

Address Matti in English. Timestamp every response. He said: **"Don't give me a
breakdown, do the work. Keep doing it"**. Use short material updates and continue
working. Do not ask to continue work that is already authorized. Do not add an
ADR or update memory without a request. Preserve source correspondence and
honest proof boundaries; passing examples are not a general theorem.

## Repository state

- Repository: `/home/tritlo/Code/mcfta`; Ubuntu/WSL2; Bash.
- Branch: `formalization/microcfta-resume-20261012`.
- Correct implementation base: **`origin/microcfta`, `4897831`**. This overrides
  older memory about `tidy/core-formula`.
- Previous pre-reset proof: **`0b0b53d`**. Its supporting checkpoints are
  `721ff6d` (full free names) and `76da95a` (probe dependency and source replay). The earlier `d630667` proof checkpoint
  rebased to `447ec5c`; its documentation checkpoint rebased to `8dc288a`.
- Restart backup: `backup/formalization-before-refresh-20261013-0418` at
  `2aacf4f`. The refresh rebased all 267 local commits without conflicts.
- Previous branch `spike/microcfta-lean-soundness` remains at `c2b1c0f`.
- Backup branch: `backup/lean-before-microcfta-20261012-2200`.
- Keep both retained stashes. The newest is `Preserve pending keyed nary and
  recursive join proofs before microcfta rebase`; its files were restored.
- Leave `/home/tritlo/Code/microecta/lean-fixes` on `fix/lean-findings` untouched.
- All proof workers froze for this handoff. Their final files are committed.
  Start new workers only when the current instructions permit them.

The earlier rebase replayed 175 proof/documentation commits. The latest
refresh preserved all 267 local commits and added upstream PR #97. Old Haskell repairs were
retired because the base contains revised upstream fixes. Do not replay those
patches. The four production repairs at the pre-reset checkpoint were:

| Commit | Repair |
| --- | --- |
| `faac0c9` | Sparse substitution returns Unknown when removing an uncertain identity replacement could expose a later duplicate formal. |
| `a38660f` | Construction tokens reject payload queries inside unfinished recursive generator callbacks. Later proof work also repaired token removal on the finite return path. |
| `4fd133f` | Grouped discovery checks final keys and minima and returns InconsistentRecursiveFamily on disagreement. |

Historical local commit `b9fde4a` supplied the fourth repair. It stops `mergeAlternatives` from recursively merging the same
union of recursive boundaries. The direct and wrapped-union witnesses now
complete. Root `FINDINGS.md` row 21 and `lean/notes-merged-narrowing.md` record
the reproduction, repair, and new source-correspondence obligations.

At 13:06 CEST, the reset continuation rebased all 274 commits onto
`origin/microcfta` at `4897831`. Backup
`backup/formalization-before-refresh-20261013-1306` preserves `8a80947`.
The rebased checkpoint is `d7de662`. All proof and counterexample files
matched the backup exactly after rebase. Conflicts kept the upstream source
and all local proofs. The Haskell packages match upstream exactly.
Upstream PRs #99, #100, and #101 include all four repairs above. PR #98
preserves up to four edges per merge group. The guard repair permits later
literal identities. Current proof updates account for both policy changes.
All 620 existing Haskell examples passed again after this refresh; see
`/tmp/mcfta-20261013-upstream-refresh-tests.log`.

Before new repository work, inspect status and refresh the correct remote base.
The continuation branch has no tracking branch. The previous successful command
was `git pull --ff-only origin microcfta`. If new upstream commits prevent a fast
forward, preserve the local checkpoint and rebase carefully; do not discard it.
Git writes need escalation in the current sandbox because `.git` is read-only.

The reset continuation found another defect in the upstream boundary return.
Calling `union` there unfolded retained recursive operands into an ordinary
node. Five recursive alternatives then grew under repeated equality passes,
and the actual public pruning call timed out. The local repair uses
`createUnion` at that return. The fixture now completes and stabilizes. It is
row 22 in `FINDINGS.md`. This is not a general convergence theorem.

## Commands and verified evidence

Pinned Lean: **4.34.1**.

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.InternedNestedProfiles
```

Latest complete audit: `/tmp/mcfta-20261013-sound-selection-audit.log`.
It checks every imported theorem against the allowlist `propext`,
`Classical.choice`, and `Quot.sound`. It rejects omitted proofs, native evaluation
axioms, and custom axioms. The count is validation evidence, not a coverage
percentage. The aggregate `Audit.lean` imports all proof modules in the current committed checkpoints.
Check new working-tree files separately until they are integrated.

Use Nix for Haskell. Nix store/lock access needs escalation. Select the coherent
linker/GMP environment with the PATH prefix below.

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test microcfta:unit-tests microcfta-generator:gen-tests microcfta-generator:refinement-tests -j1 --test-show-details=direct'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=microcfta /tmp/PROBE.hs'
```

All **620 existing examples** passed after source repair `c76d1ec`:
284 core, 194 generator, 142 refinement. Log:
`/tmp/mcfta-20261013-retained-union-tests.log`. Fourmolu checks passed for the
changed source and reproduction files. Both active Cabal-gild checks passed. Do not rerun these suites without
a new source change or unresolved failure.

The focused merge witnesses are in `lean/repro/MergedNarrowing.hs`; validation
log: `/tmp/mcfta-merged-narrowing-validation.log`. Earlier construction-query
and family-discovery logs remain useful historical evidence.

Other retained evidence:

- `/tmp/mcfta-de910ea-focused.log`: formula, nested compile, recursive reduction,
  open union, and the 285-rank two-key recurrence.
- `/tmp/mcfta-heterogeneous-join-replay.log`: heterogeneous Bool/expression join,
  eight classes, 37 member inverses, exact masses and support acceptance.
- `/tmp/mcfta-runtime-bound-source-check.log`: 4,096 projected forests.
- `/tmp/mcfta-runtime-raw-orientation-source-check.log`: 1,156 raw leaf pairs.
- `/tmp/mcfta-projected-binary-progress.log`: exact public Haskell replay with
  nested endpoints and four changing binary-class passes.
- `/tmp/mcfta-projected-three-progress.log`: convergent three-peer example that
  refutes post-first-pass row retention beyond the binary case.
- `/tmp/mcfta-source-scc-nonassoc.log`: public Haskell confirms nonassociativity
  inside a mutually reachable narrowing component.

Files under `/tmp` are supporting diagnostics and can disappear. Committed
Lean counterexamples retain the critical mathematical obstructions. None of
these finite source probes proves extraction or universal source equivalence.

## Current nested-constructor result

Start with `InternedNestedProfiles`, `InternedStoredProbeTags`,
`InternedSpecialKeyCompletion`, and `InternedPendingProfileBoundary`.
All names in this document denote files under `lean/MicroCFTA/` unless qualified.

`InternedNestedProfiles.build_profile`, `closed_heap`, and `closed_profile`
cover **arbitrary full Syntax**, including nested smart/raw binders, actual
cache hits and misses, and pending outcomes. The root profile is either opaque
or a set of literal root references. Equivalence preserves opacity and reference
membership; it does not require equal list order. The source proof derives the
stored Mu decoder invariant from its actual two probes and fresh body call.
There is no binder-free restriction or assumed callback equation.

The supporting stack includes `InternedProfileSemantics`, `ProfileCallbackForm`,
`ProfileOrigins`, `TwoProbeProfiles`, `ProbeDecoder`, `ProfileEquivalence`,
`SyntaxProbeDecoder`, `ProfileHeap`, `ProfileRequest`, and the
`InternedRootProfile*` primitive bridges. The omitted `Interned` prefix in this
list applies to every name.

`InternedStoredMuOrigins`, `InternedNestedMuOrigins`, and
`InternedProfileMuOrigins` derive the actual original Syntax, captures, both
normalized probe calls, missing-key reservation, exact fresh body call, and
historical source/profile invariants for every complete stored Mu. This works
even when the containing closed execution returns pending.

`InternedStoredProbeTags` derives, for every such stored Mu:

- Body EmptyNode iff both actual probes are EmptyNode.
- Body equal to its own reserved reference iff probes are `(Depth, Unint 0)`.
- Smart cleanup returns EmptyNode exactly in those two key cases.

`InternedSpecialKeyCompletion.closed_safe`, `closed_no_empty_key`, and
`closed_no_self_key` exclude both corresponding pending keys for **unrestricted
closed Syntax**. This is a real first-execution result, with no syntax admission
or callback-law premise. `InternedProfileReferenceInputs` derives the required
literal-alias invariance. `InternedProfileTraceSites` obtains earlier completed
nested sites from the actual depth-body trace; `SpecialKeyReadiness` uses them.

**General no-pending remains open.** `InternedPendingProfileBoundary.closed_remaining`
reduces any remaining hypothetical encounter to two opaque probes, or two pure
probes with nonempty fixed captured root references. `InternedPendingOldCall`
also retains the active fresh ancestor reference and both exact probe records
already available before that ancestor reservation.

Exact local observed replay is available through ordinary constructors, root
unions, self filtering, and cleanup. Important modules: `InternedObservedAbsence`,
`OrdinaryAbsenceReplay`, `ObservedUnionReplay`, `ObservedCleanup`,
`BoundaryFreeAge`, `CallbackTransport`, `BoundaryTransport`, and
`LiteralObservations`. They handle actual common cache extensions, old Mu
payloads, and arbitrary target sentinel aliases. The full dynamic-Mu induction
must still derive its boundary-absence premises. A root profile drops ordinary
structure and Mu identities, so it cannot alone prove exact canonical replay.

Read:

- `lean/notes-interned-special-key-completion.md`
- `lean/notes-interned-stored-mu-origins.md`
- `lean/notes-interned-root-profile-source.md`
- `lean/notes-interned-profile-reflection.md`
- `lean/notes-interned-observed-root-replay.md`
- `lean/notes-interned-boundary-transport.md`
- `lean/notes-interned-literal-observations.md`

## Full free-name semantics and the next boundary proof

`InternedFreeNameSemantics` now defines the full pure interpreter and proves
arbitrary external-name map naturality. Nodes use root profiles for empty-child
decisions. Both raw and smart binders remove the symbolic local. `InternedFreeNameForm`
derives fixed captures and optional-argument membership with captured aliases.

`InternedNestedFreeNames.build_free`, `buildMany_free`, and `buildEdges_free`
prove exact free-name membership for actual complete results, and preserve
`InternedFreeNameHeap.Heap` through complete and pending executions.
`closed_heap` derives the invariant from empty source caches.
`InternedSourceFreeNames.closed_free_empty` proves every completed closed
result has no free names.

`InternedFreeNameMuOrigins.closed_origins` retains both semantic tables at
the historical source prefix of each actual stored Mu. The exact three calls
then give `InternedStoredFreeNameBoundary.closed_reference_absent`: an old
free-name bound on the actual body excludes fresh literal boundaries in both
original probes. This applies even if the containing closed run ends pending.
See `lean/notes-interned-free-names.md`.

`InternedFreeNameTransport` gives actual source free-name transport through
arbitrary literal-name maps. `InternedProbeFreeSupport` propagates absence
through probe dependencies. `InternedProbeDependencyAge` gives strict
identity descent and well-founded induction on those dependencies.
`InternedOldProbeReplay` proves exact old-hit agreement from the two local
probe observations. The newer smart-hit case remains part of joint replay.

`InternedRequestFreeReadback.request_free` derives returned free-name
membership from the actual completed request and its final free-name heap.
It covers hits, misses, and both cleanup modes. `interned_probe_absent`
therefore excludes an absent interned name from both actual probes.

`InternedFreeAbsenceReplay.build_related` now proves full-Syntax exact raw
replay after replacing one interned literal name, when that name is absent
from the first completed result. Both completed histories must have a common
coherent cache extension. The proof includes node dead-edge removal, ordered
union operands, and dynamic Mu requests. It does not assume intermediate
replacement executions complete. The pending-site composition can require
agreement across several lexical positions, which remains active work.

`InternedLiveInputReplay.build_same` strengthens replay to arbitrary lexical
name maps. They need agree only on the pure free-name interpreter's live
input positions. `InternedLiveInputReadiness.not_pending_after_probes` then
uses an earlier completed site to exclude a later pending request, without
assuming that later binder completes. `InternedLiveInputSupport` derives the
needed agreement when every changed current input is a fresh interned name
and the actual current probe predates those names.

`InternedProbeChoiceSites.completed_site` extracts actual earlier sites along
any chosen Depth/Unint probe route. It retains each executed depth callback,
its computed Unint level, and its chronological cache growth. General pending
exclusion still needs agreement when crossed Unint levels differ. No theorem
silently treats these sentinels as fresh interned names.

**Next:** derive the fresh Mu-boundary half and compose the actual dynamic-Mu
observed replay. Free-name absence does not exclude a new closed Mu identity.
`InternedPureProfileIdentity.ordered_identity` identifies normalized pure
values in a common state when their ordered profiles agree. Set equality is
insufficient. `InternedPureProfileOrderBoundary` also shows that a warm Mu hit
can retain the earlier body's order, so exact ordered syntax correspondence
is false. Preserve these counterexamples and derive actual ordered replay.

The earlier temporary mirror search found no failure of the joint boundary
claim in 275,563 closed terms and 1,358,140 active cutoffs (eight resource
skips). That is finite model evidence only; do not use it as an assumption.

## Recursive merge and physical comparison progress

`MergedMergeTermination.wellFounded` derives a decreasing ordinary-constructor
height for guarded recursive merge calls. It does not cover the subsumption
helper or repeated-pass convergence.

`MergedPhysicalWarmup` and `MergedPhysicalComparison` derive a finite physical
comparison inventory for stored bodies that satisfy `PreparedWithoutMu`.
`MergedComparisonSource` matches the source EmptyNode and arity branches and
proves both comparison completion and successful inclusion.
`MergedPhysicalLanguage` connects that row reader to finite-run epsilon
semantics. `MergedPhysicalUnion.makeUnion_actual` proves exact union language
through the actual constructor and its final cache.

`MergedColdExecution`, `MergedColdUnfolding`, and `MergedColdInventory` remove
eager preparation from the chronological unfolding argument. Every query
completes in that structural fragment. At most the initial node counter's
number of calls can change the cache. Generated traces have a finite physical
inventory and no infinite fresh-pair descent. The ordered cold source reader
now has successful closed-root completion, resident edges with closed
children, exact returned-cache facts, and extra-fuel stability in
`MergedColdReaderFacts.read_closed`. The full ordered stateful comparison
now has completion, fuel stability, exact later replay, and actual-cache
semantic inclusion. Cold merge composition remains active. Arbitrary open nested
Mu reconstruction is still outside this structural fragment.

`MergedPhysicalGroupRoot.grouped_root_covers` derives ordinary-root language
coverage through actual group, edge, and parent constructor effects.
`MergedPhysicalGroupColumnWorker.checked_column_correct` covers actual
comparison filtering and all three child-column branches. Its recursive
certificates are restricted by ordinary height. The later `MergedAdaptiveMerge.execute_complete` now constructs those
smaller certificates and connects current-state selection to group sequencing.
Its exact initial context and source correspondence boundaries remain explicit.

`InternedProbeChoiceSites.completed_route` retains exact source bodies at
crossed binders. The closed depth counterexample now checks body/probe
depths `(1, 0, 0)` in `InternedClosedProbeCostBoundary.actual_depths`.
Do not use equality of those depths as a general source invariant.
`InternedPendingOrdinaryMismatch.closed_depth_mismatch` derives two actual
completed Depth calls of the same source body with different cached depths
from any hypothetical closed pending run. The active source origin, lexical
routes, contexts, and cache histories are all derived. The mismatch case
remains open.

`MergedSourceExposureLanguage.nodeEdges_origins` derives an actual epsilon
path for each returned edge in any extension of the returned cache.
`nodeEdges_sound` excludes introduced finite terms.
`MergedSourceExposureCoverage.actual_exact` now gives reverse edge coverage
and exact finite-term semantics in the actual returned cache. Its proof uses
exact effectless replay and a traversal-local certificate, with no global
prepared observation premise.

See `lean/notes-merged-recursion-measure.md`,
`lean/notes-merged-physical-comparison.md`,
`lean/notes-merged-physical-union.md`, and
`lean/notes-merged-cold-comparison.md`, `lean/notes-merged-cold-reader.md`,
and `lean/notes-merged-physical-groups.md`.

## Equality fixed-point termination

PR #97 (`8ac24bb`) inserts `mergeAlternatives` after every peer projection.
The current model follows PR #98: up to four distinct rows stay exact;
larger groups merge. The nullary source and complete schedule proofs use
that literal threshold.
The new `MergedProjectionBound.compiled_bound` now covers the complete
physical merged projected-leaf schedule. `MergedRawLeafSource.worker_actual`
derives the exact merged representation in the actual runtime cache.
`MergedProjectionTargets`, `Class`, `Schedule`, `Pass`, and `Termination`
compose projection, merging, seeded intersection, simultaneous edits,
required paths, class order, and the final allocation-free fixed point.
Group order is an explicit function with a complete-symbol premise. The
bound remains original occurrence weight plus one. Endpoints remain leaves.
The old `EqualityLeafProjectionRuntimeBound` is retained for the old worker.

`MergedAlternativesSubsumption` proves successful coverage checks sound;
`MergedEqualityReduction` proves constrained-language preservation with a
merge-superset premise. The physical leaf worker has a coverage theorem, and observed row order
derives complete grouping. Coverage search saturates under a finite pair
inventory. The adaptive prepared worker now has completion and physical language
coverage and fuel independence. Cold stateful comparison and selection now
have derived completion and actual-cache semantic preservation. Complete
cold merge composition remains active.
General source correspondence still needs proof. See `lean/notes-merged-narrowing.md`.

The **complete physical projected-leaf schedule** is proved for both workers. Its bound is the
original occurrence weight plus one. It includes actual endpoint reads,
first-seeded target folds, recursive ancestor edits, required paths, class
order, empty propagation, and the final allocation-free fixed point in the
actual runtime cache. Endpoints must be leaf domains; ancestors can be nested.
See `MergedProjectionBound`, `EqualityLeafProjectionRuntimeBound`, and
`lean/notes-equality-leaf-runtime-bound.md`.

The cache composition gap was repaired with raw leaf pullback and trimming of
dead occurrences. Never execute the next runtime step from a proof-prepared
cache. Source comparison also repaired the model's missing ordinary-node
operand orientation and changed the path worker to the exact source ordinary
union branch. These were proof-model repairs, not new Haskell defects.

For one fixed **binary projected class**, `EqualityFixedProjectionInvariant`
proves every original occurrence retains rows after the first reciprocal pass.
`EqualityFixedProjectionTermination.run_bounded` uses missing occurrence-row
pairs in a finite complete inventory. Nested endpoint rows are allowed. The
static row relation must be commutative and admit diagonals. The physical
adapter, original occurrence tracking, disappearing ancestor phase, and raw
normalization still need composition. See `lean/notes-equality-projected-binary.md`.

The binary invariant is false for three peers. `EqualityFixedMultiplePeers`
retains the convergent source-shaped witness and a separate abstract Steiner
cycle. The latter is not a source cycle. `EqualityFixedDegreeCounterexample`
retains the source-realizable five-degree table and nonassociativity inside a
mutual-narrowing component. An SCC cannot simply be treated as a semilattice.

`EqualityFixedRowProfile` proves local Boolean row modes after higher profiles
agree. `EqualityFixedProfileMaximum.highest_varies/prime_exists` derives a
removable maximum for one finite powerset layer over a strict-ranked row base.
**Neither theorem supplies arbitrary nested lifting.** A promising remaining
route is synchronized higher-profile induction. Generic commutative/idempotent
laws, semantic language finiteness, or a per-target rank are insufficient.
General fixed schedules with nested endpoints, three-or-more-path classes,
and interacting classes remain open. Prefixes can occur across distinct classes.

## Recursive gate rank and failed generalizations

`InternedPureProbeGate` and `InternedProbeOpacity` derive actual stored-body
unfolding completion and strict head-rank decrease when the depth probe is pure.
The other probe is then pure, its level is zero, and the actual body depth is
zero. This covers unrestricted source syntax, with source-derived premises.
The remaining general case has opaque probes. Earlier shallow, reachable-only,
closed-nested, and marker one-step theorems retain their scopes.

Do not retry these disproved shortcuts:

- `InternedOldBodyProbeAliases`: an unused old body need not equal either probe.
  Captured depth and ordinary sentinels can be filtered differently.
- `InternedNestedProbeCostBoundary` and `InternedClosedProbeCostBoundary`:
  exact free-occurrence cost coverage fails in a complete closed source-model
  cache (slot 19). The body has sentinel costs 1; both probes have costs 0.
  The closed program completes EmptyNode. Keep `FlatProbeHeap` restricted.
- `InternedSourceRankStutter`: staged scoped source-model calls with explicit
  `Depth`/`Unint 2` captures and cache prepopulation give a real modeled unfold
  with both candidate ranks `2 -> 2`. Later ranks are `[2,2,1,0]`. This is not
  divergence. It is not yet a closed empty-environment reachability theorem.
  Haskell now confirms the trace. Both actual probe substitution equations
  pass, but the unrestricted renaming law fails when its old name aliases
  the fixed depth capture. See `lean/notes-source-rank-stutter-replay.md`.
- Exact ordered root-profile equality is false. Reversed capture order can
  hit an earlier Mu pair and return the first canonical union order. The
  corrected `/tmp/mcfta-profile-order.lean` check passes; set-based `Equivalent`
  remains valid.

The open cost fixture `/tmp/mcfta-cost-probe-masked-alias.hs` also confirms both
actual-own-to-probe substitution equations in Haskell. That does not establish
the documentation's stronger equation for every captured/supplied name pair.
See the chronological `lean/notes-gate-unfolding-rank.md`.

## Preserve other completed work and remaining contracts

Typed keyed n-ary and nested heterogeneous recursive-join proofs are complete
under their stated local leaf contracts. They connect support, diagnostics,
samplers, masses, flags, inverse queries, rank ordering, and original guard
metadata. `RecursiveCompleteRecord` assembles those fields. Keep generator
members distinct from unique accepted FTA terms. Opaque Haskell builder schema,
key-discovery, codec, and productivity contracts remain explicit.

Sparse Yes now transports to complete logical satisfaction. Current pruning
and successful compiler classification inherit logical soundness and exactness
on their success domain. Backend-confirmed language equality needs backend
adequacy: a sound name-sensitive callback can give sparse Yes and complete
Unknown. The all-Int solver adapter derives its laws from correct returned
external responses. See `lean/notes-source-read-logical.md` and
`lean/notes-source-read-integer-adapter.md`.

Runtime identity lifetimes, machine words, host containers, concurrency, lazy
productivity, solver IO, PRNGs, and user codecs retain explicit correspondence
contracts. There is no verified Haskell extraction. Similarity minimization
preserves representatives; pool minimization starts a new uniform distribution.
Neither is an exact term/mass-preserving optimization under the stronger contract.

Use `lean/SYSTEM.md`, `lean/COVERAGE.md`, and `lean/API-COVERAGE.md` for the wider
ledger. All 66 Haskell modules occur in the API inventory. Keep theorem coverage,
source diagnostics, algorithmic costs, and external assumptions separate.
