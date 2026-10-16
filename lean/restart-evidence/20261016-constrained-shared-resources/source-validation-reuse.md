# Unchanged Haskell validation

Audited source main is c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e.
The preservation verifier checks all 234 starting Haskell files unchanged.
No Haskell file or package metadata changes in this checkpoint.

Reuse the strict Nix all-component build with -Werror, all six suites,
798 examples plus golden, six-file Fourmolu, and four-package Cabal-gild
and metadata checks in ../20261016-drawn-fields-local-worker/.
The original Chain reproducer output is source-derive-self-field.log there.
It returns Left (FieldAtomOnDatatype "Next" 0). Standalone holds remains
opaque for supplied pools. The derivation repair is already merged by PR #65.

These are retained source checks, not newly executed checks. No formatter
or Haskell rebuild is needed for the unchanged source. Root FINDINGS keeps
the failure, reproducer, paths, repair b9219b9e, and upstream status first.
