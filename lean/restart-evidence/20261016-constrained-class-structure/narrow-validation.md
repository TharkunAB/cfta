# Positional narrowing validation

Validated at 2026-10-16 17:07 CEST.
Source SHA-256: `1291d1d1c4fab3690e14e862e40e25d26e6f4bba7107e214d86b9e6dd1bca946`. Source length: 151 lines.

The final pinned direct check passed with exit 0 and no diagnostics in `narrow-direct-1.log`.
The parent canonical focused build passed with 767 jobs and exit 0 in `narrow-build-1.log`.
Only the historical unused `inputs` dependency warning remains in the canonical log.
All 18 public theorem axiom/signature pairs passed in `narrow-public-1.log`.
All three integration theorem axiom/signature pairs passed in `narrow-kernels-1.log`.
The final public and integration logs have no errors, warnings, or `sorryAx`.

## Checks and scope

The utilities retain the result finite ordinary domain and bound its constructor height.
They compose per-node, per-row, and ordered Language.All₂ relations.
They derive complete output forest/row domains and maximum-height bounds.
They derive actual raw makeEdge and makeNode bounds from coherent current records.
They retain original positions through literal Empty erasure and final propagation.
The relations do not assert semantic language containment.

`serial_propagation` composes two positional relations and actual final propagation, deriving output domain, original maximum-height bound, and equal length.
`raw_constructors` uses actual raw edge construction and its derived SemanticReady/residency, then actual node reconstruction. The result retains the original ordinary parent bound. Symbols, guards, and equality classes remain unrestricted.
`arbitrary_erasure` proves positional output domains and zero height without any input-domain premise.

These generic laws do not assert completed execution, a future result certificate, recursion termination, native host-demand behavior, or runtime correspondence.
Only the assigned new source and new narrow-* evidence files were changed.
The parent ran canonical Lake. Direct checks use the pinned Lean4 v4.34.1 executable and canonical `.lake/build/lib/lean` imports.
