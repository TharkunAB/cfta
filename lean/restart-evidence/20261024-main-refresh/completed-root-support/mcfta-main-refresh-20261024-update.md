## Imported main: partial program enumeration and term orders

Updated: 2026-10-24. Main: `6b62b4afef`. Merge: `78904be729`.
Read `lean/notes-current-upstream-program-enumeration.md`.

All 34 upstream paths are incorporated. All earlier Lean sources, evidence,
drafts, counterexamples and the local equality-reduction implementation remain.
The previous scan checkpoint was pushed and verified at `d501c53489`.
The backup is `codex/backup-main-refresh-20261024-0033`.

New termsPruneUntil results can be partial and need not have an accepted completion.
The shared driver changes the empty-node callback order. The old literal driver
equation needs a new correspondence bridge. Per-exclusion memo catalogs stay separate.
Phase 4 now enumerates programs and extends a typing after each fragment.
Compiled pruning, type-alternative merging, runtime specialization, parallel state
merge and optional term orders add explicit source-correspondence obligations.

Negative type-depth inputs are fixed locally in `058b11fe8f`.
Two native LPO defects remain open: a nontransitive annotated comparator and
an order reversal inside function application. FINDINGS lists both for external repair.
KBO remains the default. No partial LPO repair is presented as sufficient.

The CFTA suite passed all 325 examples. Specftacular goldens passed; they cover phase 1.
Both Specftacular libraries built with strict GHC warnings. Nine core probes passed.
A small phase-4 signature gave identical laws in serial, parallel and enumeration-ahead modes.
All three negative-depth entry checks and depth-zero checks passed.
Fourmolu and cabal-gild passed on all changed Haskell and Cabal paths.
The retained evidence distinguishes source bugs from environment and probe-harness failures.

H6 constructed_node_calls remains the strongest combined theorem under its stated premises.
No new Lean theorem or Audit run is claimed. Next, model the shared enumeration driver
and prove the no-stop bridge. The reviewed H23 scan-chain/rebuild counter proposal is retained.
Full-pipeline composition, upper resources, practical width, Haskell/solver correspondence,
the new frontend obligations and convergence remain open. The full goal remains active.
This record precedes publication of the refresh evidence and its authorized push.
