# Actual recursive Merge profile production

Validated at 2026-10-16 20:06 CEST with pinned Lean 4.34.1.

`SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer.lean` closes the general mutually recursive producer. Its three public endpoints are `run_profile`, `call_profile`, and `cold`. The actual graph fixes the exact returned heap, output, and merge memo. A call derives physical effects, physical stored entries, profile stored entries, and the complete physical/profile request contract.

No call needs an initial finite-ordinary domain premise. Its output certificate is conditional on each supplied original profile. The universal certificate includes the height-indexed row envelope and the original-relative height bound. It does not assert a finite-ordinary output for unsupported inputs.

The mutual proof uses the actual Run/Call recursor. On a miss, the first use of the smaller body Run induction hypothesis lifts the existing physical body certificate. It derives exact physical effects and both returned table invariants. The second use of that same smaller Run induction hypothesis instantiates the new local body certificate for arbitrary original row, arity, and height limits. It derives the candidate's universal certificate. Completion uses the actual current memo's first winner. It does not substitute the losing candidate's certificate for the winner's stored certificate.

`call_profile` has only these inputs: the actual completed Call, initial semantic heap facts, initial cost heap facts, initial physical stored entries, initial profile stored entries, and input availability. `cold` derives both initial table invariants for the literal empty memo. Neither endpoint takes a future body law, result law, callback, or completed child oracle. `run_profile` exposes the local code-certificate interpreter used by the mutual proof. The call endpoint discharges its body certificate internally.

Direct attempt 1 failed only because `clear` and `top` placeholders could not be inferred in a standalone `have`. Direct attempt 2 supplies them explicitly and passes with both unused-variable linters enabled. It emits no diagnostics. The failed attempt is preserved.

The root-owned `producer-finite-build-1.log` records successful canonical construction of this module at job 1282/1283. That batch then failed in the separate Finite module's namespace syntax. The Producer target itself passed without new warnings. The root accepted its canonical result. The historical `InternedFreshOrdinaryClosedCompletion.inputs` dependency warning remains distinct from the new source.

`producer-public.lean` contains all three full public signatures and axiom reports. `producer-public-1.log` passes. `producer-kernels.lean` contains three substantive integration kernels with full signatures and axiom reports. `producer-kernels-1.log` passes on its first run:

- A cold actual Call derives the output's requested profile, original-relative height, availability, and both returned table invariants.
- An actual body constructs its literal miss. The probe then constructs a warm hit using `winner_found`. The repeat uses the identical returned heap and memo and derives its own producer contract from the first call's returned facts.
- An actual body that has an earlier winner derives that winner's profile and both table invariants. No candidate certificate is supplied to the probe.

All six final signature/axiom pairs pass without errors, warnings, or `sorryAx`. Probe and source files have one terminal newline and no trailing whitespace. No older source, evidence, Audit, restart authority, Haskell file, or Git state was edited by this component.

These endpoints verify actual completed graphs. The root owns the independently constructed finite allocated wrapper and its literal worker adapters. This module does not claim a Merge constructor reservation bound, cumulative outer budget, pending-publication correspondence, or GHC forcing-order correspondence.
