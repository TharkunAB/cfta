# Validation

Validated at 2026-10-17 10:27 CEST.

- `target-forecast-direct-2.log`: absolute-path Lean 4.34.1 with all linters, exit 0, zero bytes.
- `target-forecast-canonical-1.log`: canonical target, exit 0, 1514 jobs.
- `target-forecast-public-1.log`: 43 imported full signature and axiom pairs, exit 0, no diagnostics.
- `target-forecast-kernels-1.log`: three imported pure integration pairs, exit 0, no diagnostics.

The successful probes enable explicit names, proofs, universes, deep terms, and pp.maxSteps 10000000.
Their only axioms are propext and Quot.sound, or none.
The first unsuccessful production source and its raw log remain preserved.
The current source equals direct attempt 2.
The canonical log replays the inherited InternedFreshOrdinaryClosedCompletion.lean:24 unused-variable warning.
The new production strict log is empty.
