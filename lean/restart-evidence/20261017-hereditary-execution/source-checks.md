# Current Haskell source validation reuse

Source main remains c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e.
The fresh remote readback agrees. This checkpoint changes no Haskell file.
The preservation check retains all 239 starting Haskell files and every
tracked active-package file. It reports no unexpected changed or missing file.

Reuse lean/restart-evidence/20261016-drawn-fields-local-worker/source-validation.md
and its strict Nix all-component build, 798 examples plus golden, Fourmolu,
and Cabal-gild results. No new Haskell regression or formatter run is required
for this additive Lean and restart-document checkpoint.

FINDINGS keeps the external repair handoff first. Repair b9219b9e is merged
by PR65 at c0cc8a05. The unchanged Chain reproducer returns
Left (FieldAtomOnDatatype "Next" 0). Standalone holds retains its opaque-pool
behavior. The repair rejects the invalid derivation configuration.
The historical failure block retains its exact bytes.

No additional Haskell repair or new Haskell defect occurs. Every later repair
must be recorded first in FINDINGS with its failure, executable reproducer,
affected paths, commit, checks, and upstream status.
