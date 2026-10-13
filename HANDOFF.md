# microcfta formalization restart handoff

Updated: **2026-10-13 21:56 CEST (Europe/Stockholm)**.

## Current result and read order

Read `NEXT-PROMPT.md`, this file, root `FINDINGS.md`, and
`lean/notes-source-sized.md`. The root findings are current. `lean/FINDINGS.md`
and older dated component notes are historical.

The primary `Data.CFTA.Sized` source models now prove exact accepted
node-count classes, finite reference evaluation, size-major enumeration,
and both distinct-term inverse laws. The solver-decided path preserves the
same reference order through its bound and retains the first Unknown error.
The optimized dispatcher now uses the original explicit graph rows.
**Whole-implementation verification is still incomplete.**

The repaired source and stable proofs have local commits:

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

A later commit integrates the aggregate audit and this restart package. Use `git log` for the exact latest documentation head.
Do not confuse the earlier checked checkpoint `f10fa11` with the new result.

## Authorization and allowance

Keep everything local: **no push, deployment, messages, or board posts**.
Keep the optimized interned core. Do not update memory or create an ADR without
a request. Address Matti in English. Begin each response with the actual
current timestamp. Give brief material updates. Do not ask whether to continue.

Monitor weekly allowance before work and regularly afterward:

```sh
python3 /tmp/mcfta-weekly-usage.py
```

Stop every worker and all work immediately at **1% remaining or less**.
The last observed value was **58% at 21:55 CEST**. Treat it as historical.
Check `observed_at`. The script reads 10,080-minute windows from local logs
under `~/.codex/sessions/2026/10/13`; update that date on a later restart.
It exits 99 at the threshold and 2 if usage is unavailable. Missing or stale
data is not permission to use credits.

## Repository and preservation

Repository: `/home/tritlo/Code/mcfta`, Ubuntu/WSL2, Bash.
Branch: `formalization/microcfta-resume-20261012`.
Upstream: `origin/microcfta` at **`2200117`**.
The latest `git pull --ff-only origin microcfta` reported `Already up to date.`
No rebase was needed. The starting local head was `f8a3d48`.

Before new work, read status, log, worktrees, stashes, and allowance. Preserve
a backup, pull the correct branch, and rebase if upstream has moved.
Preserve local repairs and resolve any source overlap against current code.
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
query laws. External evaluator termination and correct Yes/No decisions are
explicit contracts. Nonpositive signed bounds return an empty table.
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

All proof workers are stopped. No diagnostic process remains active.

## Remaining priorities

1. Audit the concrete source correspondence boundaries of the new Sized path:
   finite Map/Set representation, lawful equality/order, lazy table forcing,
   machine-size conversions, and evaluator IO traces. The handwritten models
   do not constitute verified Haskell extraction. Preserve the proved
   algorithmic contracts rather than assuming these runtime obligations away.
2. Complete the changed source representation bridges for PRs #104–#106 and
   #108: CPS `allBranches` with ordered branch-local state, batched suspended
   descent, omitted redundant union-find writes, and reserved empty-domain ID
   zero with adjusted machine bounds.
3. Continue the preserved constructor and equality targets below. General
   no-pending for the old constructor is refuted. General repaired first-run
   completion remains open. Saturated merge monotonicity is also refuted.
4. Retain broader probability, support, codec, and optimization contracts.
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

The aggregate audit passes **1,052 jobs and 37,335 theorem dependency checks**.
It permits only `propext`, `Classical.choice`, and `Quot.sound`.
The log is `/tmp/mcfta-sized-20261013-final-audit.log`.
Use focused targets for new work, then import finished modules into Audit.
Do not add `sorry`, native evaluation axioms, or project axioms.

The new Haskell repair passed the full generator suite with 206 examples,
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
