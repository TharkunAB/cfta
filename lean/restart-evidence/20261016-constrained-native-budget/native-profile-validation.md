# Native input profile validation

Validated: 2026-10-16 19:02 CEST.
Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryNativeProfile.lean`.
Source SHA-256: `571081b17c85907d286428de9b0cf64f8ec813218d875df51bf13634b6f7da1d`.

The module computes a uniform row and arity envelope from complete original records. The computation visits every list occurrence. Every nested ordinary node uses the same limits. Guards, canonical identities, cached depth, and cached free references have no added restriction. The finite ordinary domain excludes Mu, reference, and explicit union records.

The shape predicates derive the domain. Every domain record has its computed shape. Membership and monotonicity preserve the shape. The literal equal-symbol `Kernel.pairs` result has length at most the product of its input lengths. This bound retains repeated occurrences.

Validation:
- Canonical build: terminal exit 0, 394 jobs, `native-profile-build-1.log`.
- Direct source check: terminal exit 0, no warnings, `native-profile-direct-4.log`.
- All 31 public declarations: axiom and full explicit signature checks, terminal exit 0, `native-profile-public-1.log`.
- Five integration kernels: terminal exit 0, no warnings or `sorryAx`, `native-profile-kernels-3.log`.
- Kernels cover nested maxima with arbitrary cached metadata, duplicate join multiplicity, joined row and zipped child propagation, repeated roots and monotonicity, and construction of a completed source record with its computed shape.

The profile supplies input shape bounds. It does not establish a result profile, termination, a constructor budget, machine capacity, or Haskell runtime correspondence. Existing resident and coherent readback laws connect actual stored rows to these pure record predicates. The compiler budget uses those laws separately.

Failed direct and kernel logs remain as diagnostic evidence. The final source and final probes contain no admitted declarations. No prior proof source was edited. No Lake command ran in this task.
