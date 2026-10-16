# Independent GuardTarget review

Reviewed source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryGuardTarget.lean`.
SHA256: `4e9c66409f76ea516de406a2f49f563aa43636936c32bf1c84a95150ae7470bf`.
Canonical log: `guard-target-build-1.log`, 1353 jobs, terminal exit 0.

No material defect found.

- Lines 56–76 inspect the same actual operand receipt. The projection graph retains the original forest guard envelope. The actual merge call derives its universal guard certificate at the actual projection return. Exact node and edge table identities retain the native guard store. The physical merge store grows across the actual projection effects.
- Lines 79–106 follow head operand, recursive tail, then actual native query. The tail returns its own Ready state, stores, availability, and guard profile. `foldLimit_ge` widens the earlier head operand to the tail envelope. The native interpreter consumes the actual query trace at this same tail state. It applies one additional guard step.
- Lines 109–122 handle empty target as Empty and nonempty target through the same supplied fold reads. `targetLimit G paths` charges `paths.length - 1` native queries. A singleton target charges no native conjunction step.

The public endpoints verify supplied concrete annotated reads. They do not prove target completion or consume a future semantic law. The physical Ready and physical merge store remain initial premises. Warm native and merge guard certificates are explicit legitimate causal invariants. This module does not claim hereditary guard retention through shared target slots or through every outer family. The separate native finite adapter constructs its own receipt. Root-owned integration can combine that fact with the existing target resource constructor.
