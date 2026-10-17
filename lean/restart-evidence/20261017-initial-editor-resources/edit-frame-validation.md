# Edit frame validation

Final source SHA256: `2f88a4387a5f6d96f6358645acc955245da04e47e5f6e6288dc5ad16ab046dbb`.

- Strict absolute-path Lean 4.34.1: `edit-frame-direct-3.log`, exit 0, zero bytes.
- Canonical single target: `edit-frame-canonical-1.log`, exit 0, 1526 jobs.
- Imported API: `edit-frame-public-1.log`, exit 0, 12 complete signature/axiom pairs.
- Imported integrations: `edit-frame-kernels-1.log`, exit 0, 2 complete signature/axiom pairs.
- Both imported logs contain no errors, warnings, truncation, or `sorryAx`.
- The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- All probes print explicit full names, proofs, universes, and deep terms with 10000000 print steps.

The first two strict attempts hit elaboration heartbeat limits in the pure
Head profile helpers. The third attempt uses controlled `dsimp only` on
profile projections. The formulas and public contracts stay unchanged.
Every failed source and raw log remains. The final source uses the default
heartbeat limit. The canonical log replays an inherited dependency warning.
No imported check writes an `.olean` file. The verifier does not rebuild.
