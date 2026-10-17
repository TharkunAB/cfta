# Validation

Validated at 2026-10-17 09:49 CEST.

- `numeric-control-direct-2.log`: absolute-path Lean 4.34.1 with all linters, exit 0, zero bytes.
- `numeric-control-canonical-1.log`: canonical target, exit 0, 1239 jobs.
- `numeric-control-public-1.log`: 22 complete imported signature and axiom pairs, exit 0, no diagnostics.
- `numeric-control-kernels-1.log`: three imported integration pairs, exit 0, no diagnostics.

The successful checks use explicit names, proofs, universes, deep terms, and pp.maxSteps 10000000.
The public and integration declarations use only propext, Classical.choice, and Quot.sound, or no axioms.
The canonical log replays the inherited InternedFreshOrdinaryClosedCompletion.lean:24 unused-variable warning.
The new production strict log is empty.
The first unsuccessful production source and raw log remain preserved.
The current source equals the second strict source snapshot.
