# microcfta formalization restart handoff

Updated: **2026-10-13 17:34 CEST (Europe/Stockholm)**.

## Read first

The formalization is **not complete**. Matti requested this checkpoint to end
work safely and resume with a new agent. All three proof workers are stopped.
Do not rely on their former names or ownership after restart.

Read `NEXT-PROMPT.md`, this file, and root `FINDINGS.md`. The root findings
are current. `lean/FINDINGS.md` is historical. Detailed dated proof notes can
contain earlier open obligations that later results discharge. Use actual
theorem statements and this handoff for current scope.

The checked proof checkpoint is **`073c10c`**. Commit **`78d3d27`** preserves
two new marked drafts. Later commits contain this restart package.
The final aggregate build passed **1,026 jobs and 36,839 theorem dependency
checks**. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
The log is `/tmp/mcfta-20261013-final-restart-audit.log`.
Counts are validation evidence, not a coverage percentage.

## Objective and authorization

Continue the full intended formalization. Compile constrained languages to
exactly their valid finite terms. Prove enumeration soundness and completeness,
distinct-term ranks and both inverse laws, the requested probabilities,
optimization correctness, termination, and correspondence with current Haskell.
Do not replace this with a smaller fragment or a theorem-count target.
Generator members, accepting runs, and distinct FTA terms have separate laws.

Fix relevant implementation defects and retain counterexamples and findings.
Keep new work local: **no push, deployment, messages, or board posts**.
The earlier authorized push of `8a80947` is complete and does not authorize
another push. Do not update memory or create an ADR without a request.
Address Matti in English. Begin responses with the actual current timestamp.
Give brief material progress updates. Work without asking whether to continue.

Monitor weekly allowance. **Stop every worker and all work at 1% remaining
or less.** The last observed allowance was **63% at 17:34 CEST**. Refresh it
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
Implementation base: **`origin/microcfta` at `9508eb3`**, including PRs #102
and #103. Older `tidy/core-formula` guidance is historical.

On the latest refresh, `git pull --ff-only origin microcfta` fetched the new
base and refused to fast-forward the diverged proof branch. The explicit
`git rebase origin/microcfta` then replayed all **308 local commits without
conflicts**. Every Lean file matched the pre-rebase backup immediately after
that operation. New proof work followed it.

Before new implementation work:

1. Read status, branch, log, worktrees, stashes, and usage.
2. Preserve the current local checkpoint and the untracked native fixture.
3. Fetch the correct remote and rebase local work if upstream has moved.
4. Evaluate each new source change against the coverage ledger and actual
   executor models. Preserve every proof, counterexample, and marked draft.

The latest pre-rebase backup is
`backup/formalization-before-pr-refresh-20261013-1514` at `73b1c47`.
Keep all other `backup/*` branches and both retained stashes. Leave
`/home/tritlo/Code/microecta/lean-fixes` on `fix/lean-findings` untouched.
The isolated repair worktree `/tmp/mcfta-fresh-probe-20261013` remains on
`fix/microcfta-fresh-probe-local-20261013` at `5e6b0a7`.
Git writes need escalation because `.git` is read-only in the sandbox.

Only these source paths differ from upstream: `Interned/Operations.hs`,
`Interned/Type.hs`, and `microcfta/CHANGELOG.md`. They contain two local repairs:

- **`558b316`** retains explicit recursive child unions. It fixes the
  five-alternative public pruning timeout. Root findings row 22 records it.
- **`e0e1b37`** chooses an ordinary Mu probe above the free ordinary levels
  of the actual Depth observation. `matchMu` uses the same stored observation.
  Root findings row 23 records the closed pending-constructor defect and repair.

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

All **620 existing Haskell examples** passed with both local source repairs:
284 core, 194 generator, and 142 refinement. Nix validation used the isolated
repair checkout. The source patch is the same as root `e0e1b37`.
Fourmolu and cabal-gild checks passed. No later production code changed.

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

Temporary files are supporting evidence. Durable Lean counterexamples and
proofs are committed. Source tests and finite searches do not replace proofs.

Other remaining obligations include general recursive/equality/pruning
termination, arbitrary open nested Mu rebuilding, accepted-language and
substitution correspondence for the repaired binder, heterogeneous runtime
schema/support alignment, and concrete Haskell identity/container/concurrency/
laziness/word representations. Solver answers, PRNGs, and user codecs need
explicit external contracts. There is no verified Haskell-to-Lean extraction.
The overall result is a broad checked foundation with unresolved integration
and termination work, not whole-library verification.
