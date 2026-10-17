# Validation

Validated at 2026-10-17 09:32 CEST.

- `direct-cost-direct-4.log`: strict absolute-path Lean 4.34.1 check, exit 0, zero bytes.
- `direct-cost-canonical-1.log`: canonical target, exit 0, 1025 jobs.
- `direct-cost-public-1.log`: 15 imported full signature and axiom pairs, exit 0, no diagnostics.
- `direct-cost-kernels-4.log`: three constructed integration pairs, exit 0, no diagnostics.

All imported checks enable explicit names, proofs, universes, deep terms, and pp.maxSteps 10000000.
Their only axioms are propext, Classical.choice, and Quot.sound.
The canonical target replays one inherited unused-variable warning from InternedFreshOrdinaryClosedCompletion.lean:24.
The new source strict log is empty.
Raw unsuccessful source attempts 1 and 3 and kernel attempts 1 through 3 remain with their logs.
Direct attempt 2 is a successful intermediate core before the complete body theorem was added.
The current source equals direct attempt 4.
