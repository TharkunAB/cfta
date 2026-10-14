# Physical public entry and exact Sized query laws

Updated: 2026-10-14 23:08 CEST.
Proof: `8a0eb5f9`. Source base: `origin/main` at `f201deda`.
Repository: `git@github.com:TharkunAB/cfta.git`. Branch: `formalize`.

## Actual entry control

`SourceFreshOrdinaryNativeEntry.Execution` follows the physical root checks
before row preparation. EmptyNode returns the direct empty query record and
the identical cache. An open root returns `openAutomaton` and the identical
cache. Neither branch runs cold traversal or native callbacks.
Only a nonempty closed root collects rows and runs the native compiler.
The finite key carrier stays inside that branch. All branches return the
same public API type or the exact source error.

`SourceFreshOrdinaryColdSharedRows.Trace.unique` proves that two completed
cold traversals from the same inputs return identical rows and caches.
`SourceFreshOrdinaryColdNativeTable.for_trace` derives every final invariant
for any actual completed traversal. It requires no supplied final metadata.
`SourceFreshOrdinaryNativeEmptyApi.reference` identifies the direct empty
record with the exact reference recurrence over an empty row graph.

`execution_correct` proves that every actual public native result equals a
public reference result. It retains Ready in the returned cache. Complete
record equality includes all query functions and exact errors.
`complete` constructs finite actual execution from Ready, root availability,
normalized stored constraints, and capacity at actual reached callbacks.
It derives the completed cold traversal and all row metadata.
The physical root determines the prechecks. No arbitrary free-variable list
or final cache certificate is supplied.

## Independent language and complete query laws

`Reference.unique` proves uniqueness of the complete public result.
`Reference.success_readback` derives an exact reference graph and its
independent guarded language at the original physical root.
The proof covers the direct empty result and every successful row branch.
It does not supply a root-language equation as an entry premise.

`SourceSizedApiLaws.Exact` specifies every public query:

- Every node-count class has a finite source evaluation.
- Each class contains exactly the distinct accepted terms of that size.
- Count is the class length. Invalid signed positions return none.
- Rank exists exactly for accepted terms.
- Signed rank and unrank satisfy both distinct-term inverse directions.
- Prefixes through each size are distinct, ordered by node count, and exact.

`SourceSizedApiLaws.reference` derives the specification from the actual
reference recurrence. `Reference.exact_queries` and `Execution.exact_queries`
derive it for the physical public reference and native results.
`complete_exact` combines finite entry execution with all these laws.
`constructed_complete` derives the initial cache invariants from actual
closed construction. Checked original annotations and reached cache capacity
remain explicit. Public raw equality patterns do not normalize all inputs.

## Upstream move and preservation

The upstream is now `TharkunAB/cfta`, branch `main`. The old remote remains
as `microecta-legacy`. A conflict-free rebase replayed 575 commits onto
`f201deda`. Upstream removed the old ECTA packages and updated repository
URLs. It changed no active CFTA implementation or Lean proof file.
The active Haskell trees differ from main only in the retained four-line
constructor changelog note.

The pre-rebase snapshot is
`/tmp/mcfta-cfta-origin-refresh-20261014-2306/`. Every one of its 1,926
Lean-tree files and four root documents retained identical bytes through
the rebase. The backup branch is
`backup/formalization-complete-before-cfta-main-20261014-2309`.
All older backups, stashes, and other worktrees remain.
The three retained repro fixtures are now tracked in `452b20b5` so they
travel with the published proof history. All marked drafts remain excluded
from compilation and retained in Git.

## Validation and next work

The pinned Lean 4.34.1 aggregate audit passes 1,549 jobs and checks
dependencies of 44,339 theorems. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. The post-rebase audit log is
`/tmp/mcfta-cfta-main-20261014-audit.log`. The old unused `inputs` warning
remains. No new warning remains. No production Haskell code changed.
The previous 645 source examples and five probes retain the same active
implementation. They were not repeated for the remote and metadata changes.

Next connect the common `Exact` specification to the original-map
`sizedReference`, `sized`, and bounded solver-decided `sizedUpTo` paths.
The existing `SourceSizedFiniteKeysPublic*` and `NativeLiquid` proofs already
give exact membership, finite execution, canonical classes, order, and both
inverses. Reuse those results. Keep bounded classes empty above the bound.
Retain actual evaluator work, Unknown, and unchanged errors.
Concrete containers, lazy scheduling, external solver correctness, and
verified Haskell extraction remain explicit boundaries.

The user authorized regular pushes to `origin/formalize`. Do not deploy,
post to the board, or send messages. Check allowance regularly and stop all
work at 1% remaining or less.

Port 22 timed out during the final refresh. GitHub SSH on port 443 worked:

```sh
git -c core.sshCommand='ssh -o HostName=ssh.github.com -p 443 -o ConnectTimeout=15 -o ConnectionAttempts=1 -o ServerAliveInterval=10 -o ServerAliveCountMax=2' pull --ff-only origin main
git -c core.sshCommand='ssh -o HostName=ssh.github.com -p 443 -o ConnectTimeout=15 -o ConnectionAttempts=1 -o ServerAliveInterval=10 -o ServerAliveCountMax=2' push origin formalize
```
