# Unchanged Haskell source validation

Source main remains `c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e`.
It was merged at `896b0a1cb36c58531ee24c5b4edfff0e935111c6`.
The opening pull and fetch found no upstream delta.
This checkpoint adds no Haskell implementation, test, or behavior repair.

`verify-preservation.py` checks every starting file against
`starting-sha256.json`. It requires all 234 starting Haskell files and all
206 active package files to retain their bytes. It also checks all 2463
older non-Audit proof sources, historical repair text, and frozen manifests.
This makes the previous source validation applicable to the current source.

Reuse these passing checks from
`lean/restart-evidence/20261016-drawn-fields-local-worker/source-validation.md`:

- Strict Nix all-component build with `-Werror`, tests, and benchmarks.
- Five example suites: 321 core, 240 generator, 180 refinement, 35 GHC-fit,
  and 22 decision-model examples. All 798 examples pass.
- The hole-fit golden suite passes.
- Fourmolu passes for the six incoming Haskell files.
- Cabal-gild and package metadata checks pass for all four active packages.
- The unchanged historical Chain reproducer returns
  `Left (FieldAtomOnDatatype "Next" 0)`.

These checks were not repeated because the source did not change. The
original raw logs and reproducer retain their bytes. The recursive field-pool
repair is `b9219b9e`, merged by PR #65. Standalone holds retains its opaque
pool interpretation. The repair rejects the invalid derivation input.

Root FINDINGS.md records the failure, reproducer, affected files, commit,
validation, and upstream status first. The current source differs from main
only by the retained historical constructor changelog entry and the equality
reproducer comment. Neither is a new behavior fix. The source comparison is
saved in `source-working-diff.patch`.
