# Current merge profile code validation

Frozen: 2026-10-16 20:03 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode.lean`.
SHA256: `d15aa89ff955a28324fcbd4ee5b5878f1c49bc515956835d1894abded48e1cf6`. The file has 132 lines.

`Contract` combines the existing physical result contract with the universal profile certificate for the same complete input and result. `Certified` uses the existing exact instruction predicate with this stronger contract. `lift_certified` proves structural contract strengthening. It supplies no recursive result law.

The ordered map theorem returns `Language.All₂` over the exact input and output lists. The relation retains input-specific facts at the same actual returned heap. Its caller must prove the local instruction certificate and growth laws. The next body proof will derive those local certificates. This helper does not assert recursive completion.

The request helper passes both returned contracts to its continuation. Edge and node helpers derive physical readiness, output profiles, and height bounds from actual constructor Work. They include coherent cache hits. They derive closedness from resident profiles. They require no independent child closedness, result profile, or whole-query completion premise.

Validation:

- Direct production check: `profile-code-direct-2.log`, exit 0, no warnings. `profile-code-direct-1.log` retains an edge-height reduction error. The repair changes only the local proof.
- Canonical target: `profile-code-build-1.log`, 1127 jobs, terminal exit 0 reported by the root agent. The final log contains the successful MergeProfileCode target. This agent ran no Lake process.
- Public checks: `profile-code-public-2.log`, eight full-signature and axiom pairs, exit 0. Dependencies use only `propext`, `Classical.choice`, and `Quot.sound`.
- Integration checks: `profile-code-kernels-2.log`, four theorem/axiom pairs, exit 0, no warnings or `sorryAx`.

The kernels derive an ordered recursive-request certificate with exact multiplicity and input-relative heights; compose literal nullary edge work with duplicate-row node work; lift the complete old physical body certificate; and derive a constructor certificate on the exact warm replay heap. Initial semantic readiness and stored costs remain explicit. The failed first public and kernel logs are retained as diagnostics. Their errors do not occur in the final logs.

Direct checks use the pinned Lean 4.34.1 executable and `LEAN_PATH=lean/.lake/build/lib/lean`. The production command includes `-o /tmp/SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode.olean`. The imported public and kernel commands do not produce output files. The temporary production olean was removed after canonical validation.

The recursive body profile certificate and mutual actual Run/Call profile producer belong to separate modules. This module proves no whole-call profile, reservation bound, cumulative capacity, Haskell runtime, or concurrent-cache result. No older source or evidence file changed.
