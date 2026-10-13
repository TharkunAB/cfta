# microcfta formalization restart handoff

Updated: **2026-10-14 00:31 CEST (Europe/Stockholm)**.

## Read first

Read `NEXT-PROMPT.md`, this file, and root `FINDINGS.md`.
Then read `CONTEXT.md`, `docs/adr/0004-explicit-graph-boundary.md`, and the
component note for the chosen target. Root findings and this handoff supersede
older next-target statements. `lean/FINDINGS.md` retains historical findings.

The user requested this handoff before the context became unsafe.
**All three proof workers are stopped. No proof work remains in progress.**
The final proof checkpoint is **`9207c2cf`**. The following documentation
commit records the closing audit and these restart files. Use `git log` for
its hash. The only intentionally untracked file is
`lean/repro/NestedUnaryTwoAtom.hs`; preserve it.

## Authorization and allowance

Keep all work local. **No push, deployment, messages, or board posts.**
The earlier requested publication ended at `1f982c5b` on
`origin/formalization/microcfta-resume-20261012`. It does not authorize another
push. Do not force-update any historical remote branch.
Keep the optimized interned core and every proof, repair, counterexample,
backup, stash, marked draft, and other worktree.
Do not formalize benchmark programs, datasets, or workload specifications.
Do not update memory or create an ADR without a request.
Address Matti in English. Timestamp every response with the actual time.
Give brief material updates and work without asking whether to continue.

Monitor weekly allowance before work and regularly afterward:

```sh
python3 /tmp/mcfta-weekly-usage.py
```

Stop all work and workers immediately at **20% remaining or less**.
The last observed value was **35% at 00:31 CEST**. This is a historical value.
Check `observed_at`. The script reads the newest 40 local logs across the
current UTC date and the preceding two dates. It selects the 10,080-minute
window. It exits 99 at the threshold and 2 if usage is unavailable.
Missing or stale data is not permission to use credits.

## Repository and preservation

Repository: `/home/tritlo/Code/mcfta`, Ubuntu/WSL2, Bash.
Branch: `formalization/microcfta-rebase-20261013`.
Upstream: `origin/microcfta` at **`7989e91a`** (PR #115, shared `toRows`).
The attempted fast-forward pull reported
`Not possible to fast-forward, aborting.`
The latest user instruction explicitly authorized a rebase. It supersedes
older merge-only instructions. The 374-step rebase completed without conflicts:

```sh
git rebase --rebase-merges --reapply-cherry-picks --empty=keep origin/microcfta
```

The rebase result was `5d5ac947`. Backup
`backup/formalization-before-rebase-20261013-2315` retains `298a225b`.
`formalization/microcfta-library-20261013` also retains that checkpoint.
All 1,432 saved Lean-tree files matched immediately after the rebase.
The manifest and extra fixture copy are under
`/tmp/mcfta-rebase-20261013-2315/`. Later changes to saved files are the
intended coverage documents and audit imports; earlier proof files retain
their bytes. New proofs are separate files.

Before new work, inspect allowance, status, log, worktrees, and stashes.
Preserve a backup and refresh `origin/microcfta`. If upstream moved, rebase the
local continuation as requested. Preserve local source repairs through any
overlap. Git metadata writes require escalation in this sandbox.

Preserve the earlier backups, including
`backup/formalization-before-sized-resume-20261013-2123` (`f8a3d48`),
`backup/formalization-before-push-20261013-2200` (`6515243b`), and
`backup/formalization-before-library-refresh-20261013-2246` (`1f982c5b`).
The earlier 1,345-file manifest is under `/tmp/mcfta-resume-20261013-2123/`.
Preserve both stashes on `spike/microcfta-lean-soundness`.
Leave these worktrees untouched:

- `/home/tritlo/Code/microecta/lean-fixes`, even if reported as prunable.
- `/tmp/mcfta-fresh-probe-20261013`.
- `/tmp/mcfta-update-20261013`, including its uncommitted review merge,
  `UPSTREAM-REVIEW.md`, and `review-probes/`.

The three marked drafts remain excluded from the build and byte-identical:

| File under `lean/MicroCFTA/` | SHA-256 |
| --- | --- |
| `MergedAdaptiveStability.lean.incomplete` | `a8f71bab5b99af984c89a793cf0f153dade7fa1163fa3f18ed14e0cd08abddc9` |
| `MergedFreshOrdinarySelection.lean.incomplete` | `8630054d973629b125ce18e1e4d3f309d851e2cdb3e13e7fc71a2e6100d8a929` |
| `EqualityNestedUnaryAncestorEditCompletion.lean.draft` | `580461b034ebefd22e873a88ba2565a4e853fe901bef04280ccadb736582775e` |

The completed equality proof is a separate `.lean` sibling. Do not delete the
draft. Untracked `lean/repro/NestedUnaryTwoAtom.hs` has SHA-256
`a6c897049cdbd1f74d44dd98c99b39c63b599a4d4ef3f545886b83811f965744`.

## Main Sized contract: completed source algorithms

`SizedLanguageTheorem` proves exact distinct accepted terms at every
node-count size, finite reference class evaluation even for infinite
languages, complete size-major prefixes, and both rank/unrank inverse laws.
`SourceSizedTableEvaluation` proves finite count/plan recurrence and
canonical, ordinary-minimum, and product-minimum preprocessing.

The repaired optimized path uses the original sorted explicit rows.
Historical dead-edge and duplicate-edge counterexamples explain why interned
import could change ranks. The repair preserves the interned core.

`SourceSizedFiniteKeys*` now constructs the finite carrier from the actual
validated map keys. The original state type may be infinite. The proofs derive
root/child membership, original row readback, actual dense canonical order,
actual productivity/reachability trim keys, complete bounded table folds,
and relational occurrence traces. They retain the first Unknown and unchanged
exceptions; repeated evaluator replies need not be stable.

Current entry points:

- `SourceSizedFiniteKeysNativeLiquid.encoded_correct`: independent mixed-sort
  ambient logical acceptance, canonical order, complete bounded prefixes,
  distinct size order, and both signed inverses for the actual raw fold.
- `SourceSizedFiniteKeysNativeLiquid.encoded_finite`: finite outcomes from
  finite encoded external attempts, including errors.
- `SourceSizedFiniteKeysDispatch.nativeSized_eq`: exact raw dispatcher equality,
  including all four queries and errors. Raw prechecks and the finite raw
  key-pair synchronous product minimum test are derived.
- `SourceSizedFiniteKeysDispatch.native_success`: successful optimized results
  use the original canonical reference sequence.

The Sized optimized gate uses explicit synchronous `Language.intersect`.
It does not depend on native interned recursive intersection construction.
See `lean/notes-sized-finite-keys.md`, `lean/notes-source-sized.md`, and
`lean/notes-sized-liquid-probability.md`.

## Liquid entailment and probability

Repair **`73223201`** fixes solver name capture. Liquid Fixpoint serialized
raw names `1` and `fix$1` identically. A false quantified entailment returned
Yes. All solver-facing names now use one injective alphabetic/decimal encoding,
including declarations, variables, function heads, binders, and the default
value name. Public formula names remain unchanged.
`SourceSolverName*` proves the codec, serializer control, quantified meaning,
actual preparation, and public composition. Correct encoded Sat/Unsat replies
derive the original logical response law. The repaired native fixture returns
`(No,No,No,Yes)`. External SMT correctness, completion, and process behavior
remain explicit. See `lean/notes-solver-name-encoding.md`.
The earlier implicit ambient fresh-name repair `48024a69` and its Unknown/No
counterexample remain.

`SourceCyclicRowsProbability*` derives actual compiled cyclic sampler/PMF
records, reciprocal masses, normalization, support, signed empty-size behavior,
and sampled rank replay. It assumes no arbitrary normalized-sampler premise.
Sized class/prefix sampling, requested weights, PMF aggregation, and weighted
callback contracts are also proved. Sized sampling describes client
compositions; it does not add a Sized sampling export.

`SourceQuickCheckFrequency*` derives actual cumulative weights, finite binary
search, each ticket interval, Exact mixture agreement, and weighted sampled
rank replay. Repair **`a8b32869`** replaces the potentially overflowing index
sum with `low + (high - low) quot 2`. The repaired machine proof requires only
a representable array length. The historical 64-bit counterexample is an
arithmetic boundary, not a feasible allocated-array failure.
Uniform random draws and concrete storage remain external contracts.
See `lean/notes-quickcheck-frequency.md`.

Keep distinct FTA terms, accepting runs, generator members, and aggregated
PMF output keys separate. Metadata alone does not establish callback laws.

## Shared rows and physical construction

`SourceInternedRows*`, `SourceDenseRows*`, and `SourceRowsMinimum*` derive
finite shared traversal, exact ordered rows, validation, dense numbering,
canonical sorting, and least structural sizes from actual issued records.
`SourceCyclicRows*` connects these rows to finite class queries and inverses.
Complete custom-key ties retain original row order. Noninjective custom keys
can exchange ranks when interning order changes. Commit `17b21453` retains
Lean/native evidence and qualifies the source comments.

`SourceInternedIntersectionRows*` and `SourceInternedIntersectionDispatch*`
prove ordinary physical construction, empty/self/order control, exact common
language, finite completion, and completed memo results with actual execution
provenance. `SourcePhysicalSharedRows*` derives traversal and minimum callbacks
from resident caches. The finite plain callback needs no product-row or global
child-meet premise. Pending-thunk publication, blackholing, and full recursive
memo-effect traces remain open. A swap re-enters memoization under a reversed
key, so constructor-effect equality is not full memo-effect equality.

`SourcePhysicalRecursiveRows*` now proves actual repaired unfolding, cache
effects, stable replay, and shared rows for `mu x. (base | step x)`. It derives
an independent language of finite Chain terms from an available coherent
stored knot. It does not yet construct that initial knot or cover general Mu/union exposure.
See `lean/notes-physical-intersection-rows.md` and `lean/notes-shared-rows.md`.

## Remaining priorities

1. Extend physical recursive exposure and construction from the single-knot
   proof. Start by deriving a concrete construction witness for its stored-knot
   premises, then address general Mu/union and the native cyclic product-row
   boundary. Keep actual cache effects and finite execution in the statements.
   The raw-map Sized contract is already proved; do not redo it.
2. Complete repaired cached-depth/deep heap induction. `InternedDepthFreeProjection*`
   now proves full-syntax free-name membership and ordinary-root callback deep
   observations with nested children. `callback_observed` derives observations
   from syntax, validated context, and actual completion. General cached-depth
   and binder-heap induction remain open. Use literal environments
   `names.map Value.reference`; lists require membership agreement, not order
   equality. Do not equate predicted depth with general no-pending completion.
3. Connect bounded import to native `fromFTA`/SCC and split readback, then
   preserve supplied custom order through final observation decoders.
   `SourceBoundedImport`, `SourceFromTerms*`, and `SourceImportGroups*` already
   prove routing, denotation, finite reconstruction, arity checks, compact
   compilation, group weights, sampling, and PMFs. The ordinary shortcut's
   three-table recurrence and exact stopping order are also proved.
   Reference part order does not establish native custom decoder order.
   See `lean/notes-bounded-import.md`.
4. Extend the equality result beyond its fixed fragment. The new
   `EqualityNestedUnaryAncestorRoot*` composes actual projections, target
   merges, both ancestor edits, and the root identity stop. It terminates in
   at most `4 * (left + right) + 2` passes, with stable exact output/cache.
   Scope: one binary class, two ordinary unary ancestors, represented generated
   endpoints, and at most two initial atoms. General classes, required paths,
   the full propagation wrapper, inherited traversal, and Mu remain open.
   See `lean/notes-equality-nested-unary-root.md`.
5. Continue concrete containers, lawful equality/order, machine ranges,
   identity lifetimes, lazy execution, external solver/PRNG, and codec
   correspondence. The models are handwritten; there is no verified
   Haskell-to-Lean extraction. Keep each boundary explicit.

The old constructor's general first-run completion claim is refuted. Repaired
general completion remains open. The cold-source comparison bridge is checked.
The marked `MergedFreshOrdinarySelection.lean.incomplete` still has an `any_eq`
kernel timeout (`/tmp/mcfta-fresh-selection.log`). Try the opaque `readRows_eq`
step that resolved the analogous comparator problem. Preserve exact run
and cache equations before composing cold columns/groups/merge.

Do not use saturated merge monotonicity. The preserved counterexample has
nine versus five output terms, separated by `p(a,c)`, despite input language
inclusion and row coverage. It is not a nontermination example.
See `lean/notes-equality-merged-monotonicity.md`.

## Closing validation and checkpoint map

Pinned Lean: **4.34.1**. From the repository root:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build
```

The closing build passes **1,180 jobs and 39,689 theorem dependency checks**.
All completed modules are imported by `MicroCFTA/Audit.lean`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Log: `/tmp/mcfta-closing-20261014-audit.log`.
Use focused targets for changes, then the aggregate audit. Do not add `sorry`,
native evaluation axioms, or project axioms. Do not repeat passing checks
without a source change or a new concern.

After the solver-name repair, all **635** Haskell examples passed in Nix:
285 core, 206 generator, and 144 refinement. The native solver-name fixture,
Fourmolu, and cabal-gild also passed.
Logs: `/tmp/mcfta-solver-name-repair-20261013-tests.log` and
`/tmp/mcfta-solver-name-repair-20261013-format.log`.
After the isolated midpoint repair, all 206 generator examples passed again,
as did its arithmetic fixture and formatting. Core/refinement were not rerun
for that isolated change. Log:
`/tmp/mcfta-weighted-midpoint-20261014-tests.log`.
No production test or benchmark formalization was added in this continuation.

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test microcfta:unit-tests microcfta-generator:gen-tests microcfta-generator:refinement-tests -j1 --test-show-details=direct'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test microcfta-generator:gen-tests -j1 --test-show-details=direct'
```

Nix store/network access requires escalation. Use one coherent Nix toolchain.
The earlier 633-example run and temporary Sized regressions remain historical
in older logs; do not substitute their counts for current validation.

| Commit | Result |
| --- | --- |
| `9207c2cf` | Actual single-knot unfolding and shared rows. |
| `7e942dde` | Free-name projection and ordinary deep observations. |
| `bc7599d4` | Raw-map Sized dispatch and finite product minima. |
| `5f79d22e` | Original-state finite-map Sized execution and encoded liquid. |
| `9e429c23` | Both ancestor edits and bounded root iteration. |
| `dd038904` | Weighted backend distribution and repaired machine arithmetic. |
| `aca84882` | Physical intersection to shared-row productivity. |
| `0bc6806e` | Ordinary native dispatch and completed memo provenance. |
| `a8b32869` | Safe QuickCheck search midpoint. |
| `ea951af6` | Encoded solver requests to public liquid generation. |
| `73223201` | Injective solver name repair. |

The mathematical core and main Sized source path are strong. Remaining work
concerns substantial recursive construction and runtime correspondence, not
just documentation. Counts and passing tests are evidence, not a completion
percentage or a claim that the whole library is verified.
