# microcfta formalization restart handoff

Updated: **2026-10-13 23:43 CEST (Europe/Stockholm)**.

## Current result and read order

Read `NEXT-PROMPT.md`, this file, root `FINDINGS.md`,
`lean/notes-source-sized.md`, `lean/notes-sized-liquid-probability.md`, and
`lean/notes-bounded-import.md`, and `lean/notes-shared-rows.md`.
The root findings are current. `lean/FINDINGS.md`
and older dated component notes are historical.

The primary `Data.CFTA.Sized` source models now prove exact accepted
node-count classes, finite reference evaluation, size-major enumeration,
and both distinct-term inverse laws. The solver-decided path preserves the
same reference order through its bound and retains the first Unknown error.
The optimized dispatcher now uses the original explicit graph rows.
**Whole-implementation verification is still incomplete.**

The continuation adds the combined `SizedLanguageTheorem`, direct finite
count/plan evaluation, mixed-sort ambient liquid semantics, complete IO
outcomes, distinct term sampling, weighted replay, and public PMF semantics.
`SourceSizedLiquidAmbientPublic.public_correct` is the general liquid entry
point. It derives the evaluator law from actual per-call Sat/Unsat evidence.
Finite external attempts suffice for a finite outcome, including exceptions.
The ambient freshness repair is `48024a69`; its repaired source preflight and
historical counterexample are checked. The core and generator suites pass.

The CPS, batched descent, conditional union-find, and reserved zero-domain
source bridges are now checked. The proof note gives their exact scope.
The optimized interned core remains intact.

The bounded import fallback from PR #114 remains proved after the rebase. The new proofs cover ordered residual scans,
the exact fallback call route, complete constrained denotation effects,
ordered finite reconstruction, arity validation, finite compact compilation,
observation partitions, rank records, sampling, and PMFs.
`SourceBoundedImport.liquid_eventual` composes actual ambient denotation with
successful reconstruction and exact compact language. It derives the build
success from ranked source rows. Native interned/SCC readback, native split
representation, and custom import decoder order remain explicit boundaries.
The ordinary denotation shortcut now has its three-table recurrence, exact
empty-level stopping sequence, distinct-symbol gate, duplicate freedom, and
depth order proved. `SourceBoundedImport.plain_correct` composes that branch
with reconstruction and compact compilation without solver calls.
Do not formalize benchmark programs, datasets, or workload specifications.

The latest source is PR #115 at `7989e91a`. It replaces duplicate cyclic row
extraction with `Interned.toRows`. The requested rebase completed at
`5d5ac947`; all 1,432 saved Lean-tree files retained their bytes.
The 17 new shared-row modules prove finite traversal, exact row readback,
validated conversion, actual dense numbering, canonical stable sorting,
finite-key minimum sizes, exact cyclic classes, and both inverse laws.
`SourceCyclicRowsReadback` constructs the finite compiler input from actual
completed rows. `SourceCyclicRowsExecution` includes the minimum-size prepass.
See `lean/notes-shared-rows.md` for contracts and remaining native boundaries.

The custom-key counterexample shows that equal complete transition keys
retain source row order. Distinct symbols with the same supplied key can
exchange ranks when interning order changes. Counts and inverses still hold.
`17b21453` preserves Lean/native examples and corrects source comments.
The preceding local proof commits are `b8171aea`, `60df5ec1`, `742aab7e`, and
`1236869f`. Use `git log` for later native-gate work and documentation.

The current cyclic composition still uses the synchronous reference overlap
test. The next proof connects the actual native intersection/productivity
callback to that test. Existing `IntersectTotal` proves explicit recursive
syntax semantics. It does not derive physical interned `nodeEdges` readback.
The ordinary-node construction branch is the next concrete proof target.
Inspect `SourceCyclicRowsNativeGate*` and `SourceInternedIntersectionRows*`
for work in progress before assigning or editing those files.

The earlier Sized proof commits remain in the preserved backup history:

| Commit | Result |
| --- | --- |
| `ea73724b` | Direct explicit-row Sized dispatch and both retained native order counterexamples. |
| `54d36271` | Reference candidates, finite recurrence, equality filtering, four query laws, and canonical rows. |
| `916df01b` | Bounded decided tables, original reference order, signed queries, and trimmed guard prechecks. |
| `ccf49ce6` | Optimized graph dispatch, complete query-record equality, inverse laws, and checked counterexamples. |
| `11e66bdd` | Positive PlanScale and all existing rank partition laws. |
| `5d0c2d00` | Bounded pruning iteration and current caller preservation. |
| `be183d58` | Actual canonical preprocessing and public exact-size/query contracts. |
| `54290671` | Exact successful operational traces with varying evaluator replies. |

The earlier main-language checkpoint is `2f56d916`; its audit commit is
`4f4ca498`. The new bounded-import proof and aggregate audit checkpoint is
`274aa759`. Its preceding commits are `a13bdb03` (finite reconstruction),
`5ba5b81b` (liquid denotation), `2872ead6` (ordinary shortcut), and `c4c028ef`
(observation groups, ranks, and probabilities). Use `git log` for the later
documentation commit.
Backup `backup/formalization-before-push-20261013-2200`
preserves the earlier `6515243b` checkpoint.
Do not confuse the earlier checked checkpoint `f10fa11` with the new result.

## Authorization and allowance

The user requested **Push** earlier. That publication is complete through
`1f982c5b` on `origin/formalization/microcfta-resume-20261012`.
The new continuation uses `formalization/microcfta-rebase-20261013` and stays
local. Do not push it without a new request. Do not force-update the historical
`origin/formalization/microcfta` branch. **No deployment, messages, or board posts**.
After this requested publication, further pushes require a new request.
Keep the optimized interned core. Do not update memory or create an ADR without
a request. Address Matti in English. Begin each response with the actual
current timestamp. Give brief material updates. Do not ask whether to continue.

Monitor weekly allowance before work and regularly afterward:

```sh
python3 /tmp/mcfta-weekly-usage.py
```

Stop every worker and all work immediately at **20% remaining or less**.
The last observed value was **44% at 23:42 CEST**. Treat it as historical.
Check `observed_at`. The script reads 10,080-minute windows from local logs
under `~/.codex/sessions/2026/10/13`; update that date on a later restart.
It exits 99 at the threshold and 2 if usage is unavailable. Missing or stale
data is not permission to use credits.

## Repository and preservation

Repository: `/home/tritlo/Code/mcfta`, Ubuntu/WSL2, Bash.
Branch: `formalization/microcfta-rebase-20261013`.
Upstream: `origin/microcfta` at **`7989e91a`** (PR #115).
The fast-forward pull reported `Not possible to fast-forward, aborting.`
The latest user instruction explicitly requests a rebase and supersedes the
old merge-only instruction. The 374-step rebase completed without conflicts:

```sh
git rebase --rebase-merges --reapply-cherry-picks --empty=keep origin/microcfta
```

Backup `backup/formalization-before-rebase-20261013-2315` retains `298a225b`.
The old `formalization/microcfta-library-20261013` branch also retains it.
The rebase result was `5d5ac947` before the new proof work. Its source delta
from the backup was exactly the four upstream files. No proof or repair was
lost. The manifest and extra fixture copy are under
`/tmp/mcfta-rebase-20261013-2315/`. All 1,432 saved files matched immediately
after rebase. Subsequent proof additions and ledger updates are separate.
The original restart head was `f8a3d48`.

Before new work, read status, log, worktrees, stashes, and allowance. Preserve
a backup, and refresh the correct upstream branch. Rebase the local
continuation when upstream has moved, as requested. Preserve every local
repair and resolve any source overlap against current code.
Git metadata writes require escalation in this sandbox.

The new backup is `backup/formalization-before-sized-resume-20261013-2123`.
The earlier backup at `5eabb31` remains
`backup/formalization-before-wishlist-refresh-20261013-2109`.
The manifest and extra fixture copy are under
`/tmp/mcfta-resume-20261013-2123/`. All 1,345 earlier Lean-tree files remain.
Only `SourcePlanPositions.lean`, `SourcePlanPartition.lean`, and `Audit.lean`
changed during the new proof work, apart from the updated coverage ledgers.
All other earlier proof files and marked drafts retain their bytes.

Preserve both retained stashes and all backup branches. Leave
`/home/tritlo/Code/microecta/lean-fixes` and
`/tmp/mcfta-fresh-probe-20261013` untouched.
Preserve `/tmp/mcfta-update-20261013` and its uncommitted review merge. Its
`UPSTREAM-REVIEW.md` and `review-probes/` retain the native synthesis review
evidence. That workload review is not a benchmark formalization target.
`lean/repro/NestedUnaryTwoAtom.hs` remains intentionally **untracked**.

Preserve all three marked drafts, excluded from the build:

- `MergedAdaptiveStability.lean.incomplete`, SHA-256
  `a8f71bab5b99af984c89a793cf0f153dade7fa1163fa3f18ed14e0cd08abddc9`.
- `MergedFreshOrdinarySelection.lean.incomplete`, with the retained `any_eq`
  kernel-timeout problem.
- `EqualityNestedUnaryAncestorEditCompletion.lean.draft`, which must retain
  the exact `node_complete` result before composing edits.

Earlier local repairs remain: `807e867` retains explicit recursive child
unions; `fbc3097` repairs fresh ordinary Mu probes and stored readback.
The new Sized repair is independent of those repairs.

## Sized proof and source map

Read `lean/notes-source-sized.md` for the detailed theorem map and validation.
The main entry points are `SourceSizedPreprocessing.publicSized_eq_reference`,
`SourceSizedPreprocessing.publicSized_terms_exact`,
`SourceSizedPreprocessing.publicSized_signed_inverses`,
`SourceSizedPublicContracts.finite_class`,
`SourceSizedPublicContracts.enumeration_complete`, and
`SourceSizedDecidedPublic.public_reference_order`.
`SourceSizedDecidedOperational.public_reference_order`, `public_finite`, and
`public_first_unknown` cover per-call evaluator traces.

The old interned import can change canonical ranks by trimming dead edges or
removing duplicates. Both counterexamples remain in Lean and native fixtures.
The repaired `sized` uses `Table.tableIndex` and `Table.tablePosition` on the
same original sorted rows as the reference. Its finite product-minimum scan
derives unambiguity. It no longer calls `fromFTA` or `rowsOf`.
The interned construction and optimization core remains unchanged.

`SourceSizedDecided*` derives the actual frozen table fold, first Unknown
error, original trim-state inventory, full ordered class agreement, and all
query laws. The general fold retains evaluator contracts; the new ambient
liquid proof derives those contracts from the actual adapter and external
Sat/Unsat response evidence. Nonpositive signed bounds return an empty table.
The relational operational proof permits different replies to repeated
queries. Successful traces are exact under per-call adequacy. Finite
per-call result witnesses give a finite bounded result, including errors.
No stable reply function is required. Completion is an existence theorem
under that explicit witness contract.

`SourcePlanPositions.Plan` now has positive scaling. Existing replay,
partition, nodup, total count, and bounded size proofs include it.
`SourcePlanScale` connects valid quotient selection and grouped node counts.
Do not remove the valid-counted-size premise from raw source selection.

`BoundedPruningFix` and `BoundedPruningCaller` cover current local budgets.
A new recursive body resets its budget to 64. Only a direct revisit decreases
its local budget. Per-call and recursive callback termination remain separate.
Do not claim that a local budget establishes whole-pruning completion.

Native overlap-gate and ordinary intersection-row proofs are in progress.
Check worker and process status on restart; do not assume they are stopped.

## Remaining priorities

1. Connect the native cyclic overlap callback to the proved finite
   synchronous overlap gate. Continue the ordinary-node intersection branch
   through hash join, child operations, edge/node construction, and stored
   readback. Do not replace this obligation with an opaque language premise.
   Then audit the concrete source correspondence boundaries of the Sized path:
   finite Map/Set representation, lawful equality/order, lazy table forcing,
   machine-size conversions, and evaluator IO traces. The handwritten models
   do not constitute verified Haskell extraction. Preserve the proved
   algorithmic contracts rather than assuming these runtime obligations away.
2. Connect the new bounded fallback to native import readback. Start from
   `SourceFromTerms.build_rows` and `SourceFiniteRebuild.dependency_wellFounded`.
   Derive the actual `fromFTA`/SCC and split readback, then preserve the supplied
   custom order through `Flat.fromAutomaton` and final observation ranks.
   `SourceImportGroupsCompiler` proves a sorted finite reconstruction of each
   part; it does not identify that order with the native part decoder.
   Complete constructor-row exposure and whole lazy enumeration still need
   separate source contracts. Preserve the new CPS and bounded proofs.
3. Continue the preserved constructor and equality targets below. General
   no-pending for the old constructor is refuted. General repaired first-run
   completion remains open. Saturated merge monotonicity is also refuted.
4. Retain the new mixed-sort liquid and PMF/sampling contracts. Solver
   correctness/completion and lawful random backends remain explicit. The
   public Sized sampling results describe client compositions, not a new API.
   Continue broader support, codec, and optimization contracts.
   Distinct FTA terms, accepting runs, and generator members remain separate.

## Preserved secondary targets

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

The completed shared-row audit passes **1,123 jobs and 38,793 theorem dependency checks**.
It permits only `propext`, `Classical.choice`, and `Quot.sound`.
The log is `/tmp/mcfta-one-row-20261013-audit.log`. All 17 completed shared-row
modules are imported. New native-gate work needs a new aggregate audit.
Use focused targets for new work, then import finished modules into Audit.
Do not add `sorry`, native evaluation axioms, or project axioms.

The rebased source passed 285 core, 206 generator, and 144 refinement examples
in Nix. Log: `/tmp/mcfta-one-row-20261013-tests.log`.
Fourmolu and cabal-gild checks passed in Nix.
Log: `/tmp/mcfta-one-row-20261013-format.log`.
The separate-process custom-key reproduction passed.
Log: `/tmp/mcfta-key-ties-20261013.log`.
The only current production change qualifies ordering comments. No production
test or benchmark formalization was added. Do not repeat these passing suites
without a new source change or concern.

The earlier Sized repair passed the full generator suite with 206 examples,
including two temporary regression cases. The permanent suite remains at
204 examples. The temporary patch is
`/tmp/mcfta-resume-20261013-2123/sized-regressions.patch`.
Both native fixtures and both checked Lean counterexamples are committed.
Fourmolu and cabal-gild checks passed in Nix. No new production test was committed.

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test microcfta-generator:gen-tests -j1 --test-show-details=direct'
```

The earlier pre-continuation full source run passed 633 examples: 285 core,
204 generator, and 144 refinement. Core and refinement were not rerun for
the isolated Sized change. Do not report that old combined run as new evidence.
Its log remains `/tmp/mcfta-20261013-2109-rebase-tests.log`.
Nix store access requires escalation. Do not repeat passing tests without
a source change or a new unresolved concern.

Runtime identity lifetimes, concrete containers, host allocation, lazy sharing,
machine words, solver IO, PRNGs, and user codecs remain explicit boundaries.
There is no verified Haskell-to-Lean extraction. General repaired construction,
open nested Mu reconstruction, and whole recursive pruning remain unfinished.
Temporary logs support the durable committed proofs and counterexamples.
