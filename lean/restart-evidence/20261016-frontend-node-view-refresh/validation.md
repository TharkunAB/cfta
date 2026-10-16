# Frontend source refresh checkpoint

Previous goal turn: PROGRESS. Current goal turn: PROGRESS. The full-library
formalization goal remains active. No whole-library theorem is completed.

## Source and proof boundary

Source main advanced from `ccebf0f7` to `999c04a5` after the preceding
`b931bcc6` publication. The bounded fetch completed before the merge.
Backup branch `backup/formalize-before-main-999c04a5-20261016-1301` retains
that published head. Merge `9aaffc95` completed without conflict.

PR #60 adds field pools. PR #61 changes typing rules to node views. PR #62
fixes negative bounds. Nine generator files change, including seven Haskell
files. The interned core, equality operations, Sized, GHC package, decision
model, and Lean sources retain their bytes. No local behavior repair is made.
Root FINDINGS.md records the upstream negative-bound repair first, including
its two invalid-bound cases and the zero-bound control.

Pinned Lean 4.34.1 builds `MicroCFTA.Audit` with terminal exit zero: 2444 jobs
and 58082 dependency checks. `audit.log` records the result. The only warning
is the old unused `inputs` binding. The permitted foundations remain
`propext`, `Classical.choice`, and `Quot.sound`. The unchanged Audit does not
prove the newly merged frontend adapters.

## Current Haskell validation

`source-validation.md` and `source-validation-inputs.json` record the exact
Nix commands. The strict all-component build enables tests and benchmarks
with `-Werror` and exits zero. All six suites exit zero: 791 examples with
zero failures, plus the hole-fit golden check. The counts are 321 core,
238 generator, 175 refinement, 35 GHC-fit, and 22 decision-model examples.
Fourmolu passes on seven changed Haskell files. Cabal-gild and metadata
checks pass on all four active packages. No test file is changed locally.

The single Haskell build slot was released after the actual suite process
terminated. The hoogleplus recovery was unnecessary. The existing dynamic
symbol linker warning remains. The current run replaces the previous
788-example source result; that older result is not reused for new source.

## Independent source checks and counterexample

`typing-audit.md` records actual node extraction, validation order, callback
constructor selection, and retained needed-type discovery. Reached malformed
callbacks now validate before bound filtering. The old row model needs a
per-reached-node adapter because new callbacks can select constructors.

`derive-audit.md` records exact Constructor keys, field maps, precedence,
annotation checks, shape checks, and value evaluation. The imported-automaton
path deliberately takes terms from the automaton rather than the field pool.
That documented behavior is not reported as a pool-membership defect.

Root then ran `derive-self-field-draft.hs` inside Nix. The first sandboxed
attempt exited one because the Nix database lock was read-only. The retry
used the required Nix access and exited zero. Tool session 73352 was polled
to that terminal result. The two raw logs retain both outcomes.

The successful output confirms `(field holds, type-wide holds, independent
all-node invariant) = (True, True, False)`. The high-level field-local
derivation succeeds and generates `Next (End False)`. The old type-wide
replacement instead rejects root annotations as `UnknownConstructors`.
Root FINDINGS.md records this as confirmed and unfixed. The every-node
contract and opaque supplied-subtree interpretation need a semantic decision.
No behavior repair is inferred from passing suites. The frozen draft and
its earlier review remain unchanged; the additive confirmation records the
later executed result.

## Preservation and restart

`verify-preservation.py` checks all 5097 starting tracked files. All 2443
older non-Audit Lean sources and Audit retain their bytes. Only the nine
exact upstream paths and seven restart authorities can change. Twenty-five
frozen manifests verify 201 module entries. All four prior repair bullets
and the PR #55 handoff remain byte-identical. The two new entries precede
that historical block. Stashes and the three other worktree records remain.

The raw `starting-worktrees.txt` retains its final blank separator. Exclude
that raw capture from source whitespace checks. No failed draft or raw log
is deleted. Unavailable earlier external drafts are not claimed recovered.

Read `lean/notes-frontend-node-view-refresh.md`, then the preceding
`20261016-current-conjunction-worker/scan-worker-next.md`. Implement literal
first-seeded queries and Scan next. Then compose local reduction, required
children, parent construction, and the mutual outer worker. General
constrained termination, unequal-length path classes, repeated passes,
frontend composition, exact Sized and probability contracts, concrete host
execution, and older constructor/equality targets remain open.

Preserve the optimized interned core, all proofs, counterexamples, repairs,
and marked drafts. Record every later Haskell repair first in root FINDINGS.
Push verified formalize checkpoints regularly. No board posts or deployments.
