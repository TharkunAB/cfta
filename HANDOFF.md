# microcfta formalization restart handoff

Updated: **2026-10-13 21:18 CEST (Europe/Stockholm)**.

## Read first

The formalization is **not complete**. This checkpoint rebases the proofs onto
the new exact-size APIs and records the next proof targets. All proof workers
are stopped. Do not rely on former worker names or ownership after restart.

Read `NEXT-PROMPT.md`, this file, and root `FINDINGS.md`. The root findings
are current. `lean/FINDINGS.md` is historical. Detailed dated proof notes can
contain earlier open obligations that later results discharge. Use actual
theorem statements and this handoff for current scope.

The rebased checked proof checkpoint is **`f10fa11`**. Commit **`1a8a27e`**
preserves two marked drafts. The previous restart package rebased to `dc9f212`.
Later commits update these documents. The refreshed aggregate build passed
**1,026 jobs and 36,839 theorem dependency checks**.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
The log is `/tmp/mcfta-20261013-2109-rebase-lean.log`.
Counts are validation evidence, not a coverage percentage.

No Lean definition or theorem changed in this refresh. The successful audit
does not establish correspondence with the new Haskell implementations.

## Objective and authorization

Prioritize Matti's main contracts: generate exactly the described finite terms,
finish each requested size class, enumerate by node-count size, and prove both
rank/unrank inverse laws for distinct terms. Connect these results to the new
`Data.CFTA.Sized` API. Preserve the broader probability, optimization, and
constructor proof work. Optional optimization convergence is secondary when
the exact graph path does not call that optimization.
Generator members, accepting runs, and distinct FTA terms have separate laws.

Read `docs/adr/0004-explicit-graph-boundary.md`. The decision keeps the optimized
interned core. Exact queries use the explicit graph as their semantic boundary.
Do not restart a replacement of the whole interned core from the earlier wishlist.

Fix relevant implementation defects and retain counterexamples and findings.
Keep new work local: **no push, deployment, messages, or board posts**.
The earlier authorized push of `8a80947` is complete and does not authorize
another push. Do not update memory or create an ADR without a request.
Address Matti in English. Begin responses with the actual current timestamp.
Give brief material progress updates. Work without asking whether to continue.

Monitor weekly allowance. **Stop every worker and all work at 1% remaining
or less.** The last observed allowance was **62% at 21:17 CEST**. Refresh it
before work; this is a historical snapshot.

```sh
python3 /tmp/mcfta-weekly-usage.py
```

The script exits 99 at the threshold and 2 when usage is unavailable. It reads
`event_msg` / `token_count` rate limits with a 10,080-minute window from local
Codex logs. Its current directory is `~/.codex/sessions/2026/10/13`; update
that date on a later restart. Check `observed_at` for freshness. Missing or
stale data is not permission to consume credits.

## Refresh and preserve

Repository: `/home/tritlo/Code/mcfta`, Ubuntu/WSL2, Bash.
Branch: **`formalization/microcfta-resume-20261012`**.
Implementation base: **`origin/microcfta` at `2200117`**, including PRs #104
through #113. Older branch and base instructions are historical.

On the latest refresh, `git pull --ff-only origin microcfta` fetched the new
base and refused to fast-forward: `fatal: Not possible to fast-forward,
aborting.` The authorized `git rebase origin/microcfta` then replayed all
**339 local commits without conflicts**. All **1,345 preserved Lean-tree files**
matched their SHA-256 manifest immediately after rebase. This includes every
proof, counterexample, marked draft, and the untracked native fixture.

Before new implementation work:

1. Read status, branch, log, worktrees, stashes, and usage.
2. Preserve the current local checkpoint and the untracked native fixture.
3. Fetch the correct remote and rebase local work if upstream has moved.
4. Evaluate each new source change against the coverage ledger and actual
   executor models. Preserve every proof, counterexample, and marked draft.

The latest pre-rebase backup is
`backup/formalization-before-wishlist-refresh-20261013-2109` at `5eabb31`.
The manifest and a second copy of the untracked fixture are in
`/tmp/mcfta-rebase-20261013-2109/`.
Keep all other `backup/*` branches and both retained stashes. Leave
`/home/tritlo/Code/microecta/lean-fixes` on `fix/lean-findings` untouched.
The isolated repair worktree `/tmp/mcfta-fresh-probe-20261013` remains on
`fix/microcfta-fresh-probe-local-20261013` at `5e6b0a7`.
Git writes need escalation because `.git` is read-only in the sandbox.

Only these source paths differ from upstream: `Interned/Operations.hs`,
`Interned/Type.hs`, and `microcfta/CHANGELOG.md`. They contain two local repairs:

- **`807e867`** (formerly `558b316`) retains explicit recursive child unions. It fixes the
  five-alternative public pruning timeout. Root findings row 22 records it.
- **`fbc3097`** (formerly `e0e1b37`) chooses an ordinary Mu probe above the free ordinary levels
  of the actual Depth observation. `matchMu` uses the same stored observation.
  Root findings row 23 records the closed pending-constructor defect and repair.

## New source and its proof impact

| Change | Source status | Formalization work |
| --- | --- | --- |
| PR #107: `Data.CFTA.Sized` | `sizedReference` supplies distinct exact-size terms, counts, and inverse queries. Cycles, overlap, and path equalities use the same finite recurrence. `sized` uses the count table where the ordinary unambiguous import succeeds. | Model the new reference worker and prove its exact class sequence. Compose the optimized branch with that sequence. No new Sized API theorem exists yet. |
| PR #112: `sizedUpTo` | Builds classes through a bound and checks every candidate transition constraint. `Unknown` returns `GuardUnknown`; classes above the bound are empty. No pruning is called. | Prove the finite table fold and successful exactness under a terminating, adequate guard evaluator. Unknown must remain an error. |
| PR #109: pruning budgets | `fixWithin` bounds transition narrowing to 64 calls. `pruneNodeWithin` bounds repeated rebuilding of each recursive node. Guards remain attached when a budget ends. | Prove bounded iteration from per-pass preservation and completion. A pass budget alone does not prove termination of each pass, constructor, or solver call. General identity convergence is no longer a prerequisite for these bounded loops. |
| PR #110: transformation contracts | `CONTEXT.md` distinguishes exact transformation, over-approximation, and representative selection. | Keep these contracts separate. Existing counterexamples remain evidence against stronger claims. |
| PR #113: explicit graph boundary | ADR 0004 selects `Data.CFTA.FTA` for exact queries and retains interned construction. | Prove the direct graph path first. `sized` still converts through `fromFTA` in its optimized branch, and the cyclic import still uses `rowsOf`. The adapter consolidation is not implemented by the ADR. |
| PR #111: repeated child sizes | `PlanScale` counts a selected child once for each position that contains it. Values and ranks stay unchanged. | Extend source plan/size correspondence for positive scaling. Existing Lean plans have no `PlanScale` case. |
| PRs #104–#106 and #108 | CPS enumeration, batched constraint descent, omitted redundant union-find writes, and reserved empty-domain identity. | Add the local representation bridges listed in root findings. Prior checked models have not changed automatically. |

The current source test suites pass **633 examples**: 285 core, 204 generator,
and 144 refinement. The generator suite includes the new size API and four
300-case properties. These tests do not replace the new correspondence proofs.

## Files that must survive restart

All stable proof modules are committed and imported by `MicroCFTA/Audit.lean`.
Three marked files are committed and excluded from builds:

| File | Status and next use |
| --- | --- |
| `lean/MicroCFTA/MergedAdaptiveStability.lean.incomplete` | Original marked draft. Preserve unchanged. Its completed sibling proves fuel independence. SHA-256: `a8f71bab5b99af984c89a793cf0f153dade7fa1163fa3f18ed14e0cd08abddc9`. |
| `lean/MicroCFTA/MergedFreshOrdinarySelection.lean.incomplete` | Proposed repaired selection bridge. `any_eq` reaches a kernel timeout; `retain_eq` then lacks that constant. See the comparison note. |
| `lean/MicroCFTA/EqualityNestedUnaryAncestorEditCompletion.lean.draft` | Unfinished semantic composition of actual ancestor edits. `complete_mono` hides the exact run needed by the proof. See the ancestor replay note. |

`lean/repro/NestedUnaryTwoAtom.hs` is intentionally **untracked**. Preserve it
with untracked files before rebase. It passed 4,352 native cases. It is a
local positive diagnostic and was not committed as a new source test.
No worker or diagnostic process remains running.

## What is checked

- Independent constrained finite-term semantics, FTA acceptance, enumeration,
  exact distinct-term indexing and inverse laws, and rational probability laws.
- Executable enumeration and symbolic count/select/rank drivers, supported
  lattice operations, typed recursive/mutual/n-ary families and nested joins.
  Their representation and external premises remain explicit.
- Formula substitution, logical guard transport, source pruning components,
  recursive gates, and retained implementation counterexamples. Representative
  minimization is not exact language or mass preservation.
- PR #102 flat memo probing, copying, growth, winner retention, and bounded
  node/domain key representation. PR #103 maintained waiting/expandable indexes,
  source mutation updates, exact scheduler selection, and bounded word arithmetic.
- Cold-reader completion and exact finite language; ordered comparison and child
  selection; complete cold merge completion, coverage, exact two-fuel stability,
  original-cache language transport, and exact successful replay in later caches.
  The prepared fragment is explicit. It permits closed nested Mu leaves but
  excludes reconstruction through open nested Mu records.
- Repeated target merging reaches an exact value-and-cache fixed point within
  ordinary height for finite ordinary trees. This is not the whole equality loop.
- A concrete nested unary projected endpoint loop with at most two original
  residual atoms terminates within `4 * (leftOccurrences + rightOccurrences) + 2`
  passes. Its unions, merges, intersections, compiler, and identity test are
  executable. Ancestor replay now uses the actual returned edit cache.

The full inventories are `lean/COVERAGE.md` and `lean/API-COVERAGE.md`.
They do not assert that every Haskell path is verified.

## Constructor discovery and current repair

`InternedClosedPendingBoundary` **refutes universal closed completion of the
old constructor executor**. A scoped structural program reaches pair `(86,86)`
with reserved identity 87, absent payload, and next counter 92. No callback
inspects its argument. Two independent native translations time out after five
seconds at root WHNF. Native evidence is bounded noncompletion; the kernel
separately proves the exact model pending result.

The original executor and all old provenance/depth counterexamples remain.
Do not keep trying to prove unrestricted no-pending for that executor.
Read `lean/notes-paired-pending-boundary.md`.

The local repair's two failing fixtures complete in Lean. All five native
probes and all 620 existing Haskell examples pass. `InternedFreshOrdinary*`
now derives cache Facts, normalization, actual source origins, exact stored
probe readback, root profiles, free-name heaps, closed-output free-name absence,
chosen capture bounds, source set-fold agreement, bounded signed arithmetic,
and exact completed constructor replay. Historical semantic contexts retain
all effects, including discarded computations.

The original Depth observation has exactly the complete Mu's free ordinary
names. Each such level is below the selected probe. This alone does not prove
that a discarded intermediate computation avoids all relevant aliases.
General repaired first-run completion remains open.

Read these notes in order:

1. `lean/notes-fresh-ordinary-candidate.md`
2. `lean/notes-fresh-ordinary-records.md`
3. `lean/notes-fresh-ordinary-profiles.md`
4. `lean/notes-fresh-ordinary-free-names.md`
5. `lean/notes-fresh-ordinary-contexts.md`
6. `lean/notes-deep-free-depth.md`

## Exact next proof targets

### First: exact size classes and their rank API

Start with `microcfta-generator/src/Data/CFTA/Sized.hs`. Reuse
`RecursiveSize`, `SizedRank`, `DistinctRank`, `FTAValidation`,
`SourceEqualityGuards`, `SourceCyclicAutomaton`, and `SourceSymbolicStableIndex`.
Their current statements do not yet cover the new module.

1. Model `candidates`, including reversed child traversal and ascending
   left-size splits. Prove node-count exactness and strict child-size descent.
2. Model `sizedReference`: sorted rows, equality checks, and first-occurrence
   `nubOrd`. Prove finite class construction, no duplicates, and membership
   iff the original graph accepts the term at that size. Derive all four
   `fromClasses` query laws and signed invalid-size/rank behavior.
3. Prove `sizedUpTo` by induction on size and the finite state fold. Retain the
   original constraints and the exact Unknown error. State evaluator
   termination and semantic adequacy explicitly. Derive empty classes above
   the bound. Do not claim unconditional termination of an external solver.
4. Prove that successful `sized` count-table dispatch agrees with the same
   sequence, not only its language. Include canonical row ordering, source
   prechecks, `fromFTA`/`rowsOf`, and valid class-rank selection. The existing
   `SourceCyclicAutomaton.exact_index_api` is a strong component here.
5. Expose a size-major stream theorem from the class interface. Do not stop
   at the first empty size. Preserve the distinction from depth enumeration
   and from finite generator ranks whose order is not size-major.

After the direct graph contract, prove `toFTA` on finished closed inputs as
the semantic adapter. Construction of arbitrary interned inputs remains its
own theorem. The optimized Sized branch still needs its actual adapters.

### Then: changed source interfaces

- Extend `SourcePlanPositions.Plan`, `position_replay`, and
  `SourcePlanPartition.partition_exact` with positive `PlanScale`.
  `CompactGroups.childGroups_nonempty` supplies positive group multiplicity.
  A repeated child contributes `positions.length * childNodeCount` nodes.
- Prove `fixWithin` preserves an invariant through at most its budget of
  completed calls. Compose existing per-pass exactness with the actual
  bounded pruning caller. Keep individual-call termination separate.
- Bridge CPS `allBranches` to `EnumerationState` with ordered results and
  branch-local states. Bridge batched descent to `EqualityTrie.descendScs_exact`.
- Bridge the omitted union-find write to the same extensional forest.
  Reserve domain ID zero and prove nonempty raw IDs plus one remain distinct
  and in range for `IntersectionFlatMemoKeyDomain`.

### Preserved secondary targets

The following work remains valid and unfinished. Resume it when required by
the chosen exact API path or after the primary size/rank contract. General
unbounded equality convergence is not the first restart task.

### Repaired constructor depth and completion

`InternedDepthSemantics` has a pure full-syntax interpreter for root names,
deep names, opacity, and Mu depth. External maps need not be injective.
`arguments_depth` gives equal predicted depth for literal callback arguments.
`InternedDeepFreeDepth`, `InternedDeepFreeNormalization`, and
`InternedDeepLocalNormal` connect actual filtering and cleanup to deep local
occurrences. Root self filtering preserves depth exactly.

`InternedDepthSemanticProjections` now proves coherent-shape preservation and
exact projection to the existing profile interpreter. **Free-name membership
projection is not yet written.** Lists can differ in order, so prove membership
agreement, not literal list equality.

`InternedFreshOrdinaryDepthHeap.candidate` and
`InternedFreshOrdinaryDepthRequest.request_checked` prove local candidate/hit/
miss/pending laws. They still take recursive observation premises. Next derive
full syntax induction over literal environments `names.map Value.reference`.
Use the existing profile/free proofs, pure projections, ordered child/edge
maximum-depth composition, and `arguments_depth`. This should derive the full
depth/deep heap without recursive callback premises. Then continue general
no-pending; do not treat predicted depth equality or finite searches as that proof.

### Repaired cold-source correspondence

`InternedFreshOrdinaryStoredSubstitution` proves exact old/new execution for
binder-free prepared reconstruction. `MergedFreshOrdinaryExposure` transfers
actual reader results, errors, caches, and completion. The complete
`MergedFreshOrdinaryComparison.check_eq` now transfers every ordered comparator
result for closed prepared available operands.

Resume the marked selection draft. Its latest kernel-timeout log is
`/tmp/mcfta-fresh-selection.log`. `compare_bind_eq` and `compare_context` did
not fix the `any_eq` proof term. The comparator's own analogous timeout was
resolved by an opaque `readRows_eq` step before induction. Preserve actual
execution equations while simplifying the selection proof. After it checks,
compose selection through cold columns, groups, and the complete merge worker.
Read `lean/notes-fresh-ordinary-exposure.md` and
`lean/notes-fresh-ordinary-comparison.md`.

### Nested equality ancestor composition

The frozen `EqualityNestedUnary*` stack includes physical endpoint construction,
intersection, projection union, current merging, a concrete schedule, and its
bound. `AncestorReplay.actual_original` replays all original child/edge/parent
requests in the actual returned edit cache. `AncestorState.edit_stored` retains
original finite indices. `AncestorEdit.node_complete` supplies concrete effects.

Resume `EqualityNestedUnaryAncestorEditCompletion.lean.draft`. Destruct
`node_complete` directly to retain its exact run. Rewrite with `node_eq`, apply
`edit_stored`, and use `WorkFacts.meet_correct` at each original index. Then
compose both forest edits and the root identity stop test. The endpoint bound
is proved; the whole root loop is not yet composed. See
`lean/notes-equality-nested-unary-ancestor-replay.md`.

Generalize beyond fixed unary/two-atom and single-class fragments afterward.
A finite state carrier alone does not exclude cycles.

### Do not use the disproved merge shortcut

`EqualityMergedTargetMonotonicity.saturation_not_monotone` disproves monotonicity
of saturated target merge under language inclusion and source row coverage.
Five explicit pairs and a two-row compact encoding have the same five native
terms. Their already-stable merges have nine and five terms. `p(a,c)` separates
them. Lean checks input inclusion and actual-cache output separation. This is
not a nontermination example. Read `lean/notes-equality-merged-monotonicity.md`.

## Validation and broader boundaries

Pinned Lean: **4.34.1**.

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build
```

The final audit is green. New unfinished files are deliberately excluded.
Use focused targets while repairing them, then import finished modules into
`Audit.lean`. Do not add `sorry`, native evaluation axioms, or custom axioms.

All **633 existing Haskell examples** passed in this rebased checkout with
both local source repairs: 285 core, 204 generator, and 144 refinement.
Fourmolu checked the changed production Haskell files. Cabal-gild checked the
changed generator package file. Both checks passed. No new source test or
production change was made during this refresh.

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test microcfta:unit-tests microcfta-generator:gen-tests microcfta-generator:refinement-tests -j1 --test-show-details=direct'
```

Nix store access needs escalation. Do not repeat the suite without a new source
change or unresolved concern. Relevant evidence:

- `/tmp/mcfta-fresh-probe-validation.md` and `/tmp/mcfta-fresh-probe-620-tests.log`
- `/tmp/mcfta-paired-pending-source-validation.md` and `/tmp/mcfta-paired-pending-open.hs`
- `/tmp/mcfta-flat-memo-probe.log`
- `/tmp/mcfta-merge-monotonicity.log`
- `lean/notes-equality-nested-unary.md` for the retained native fixture log
- `/tmp/mcfta-20261013-2109-rebase-lean.log` for the refreshed aggregate audit
- `/tmp/mcfta-20261013-2109-rebase-tests.log` for all 633 source examples
- `/tmp/mcfta-20261013-2109-rebase-format.log` for formatting checks

The older probe logs describe their named earlier baselines. The full suites
above were rerun after this rebase; individual old temporary probes were not.

Temporary files are supporting evidence. Durable Lean counterexamples and
proofs are committed. Source tests and finite searches do not replace proofs.

Other remaining obligations include completion of individual pruning calls,
general unbounded equality convergence, arbitrary open nested Mu rebuilding, accepted-language and
substitution correspondence for the repaired binder, heterogeneous runtime
schema/support alignment, and concrete Haskell identity/container/concurrency/
laziness/word representations. Solver answers, PRNGs, and user codecs need
explicit external contracts. There is no verified Haskell-to-Lean extraction.
The overall result is a broad checked foundation with unresolved integration
and termination work, not whole-library verification.
