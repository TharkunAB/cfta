# LowerProfiles validation

2026-10-16 22:17 CEST.

Production source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryLowerProfiles.lean`, 164 lines, SHA256 `1292b828fcbd51a2d0a28dcd35b1d3fe40361683c9e4a6822970f569e7cf5909`.

- Pinned direct Lean: exit 0, `lower-profiles-direct-1.log`, no diagnostics.
- Root canonical Lake: exit 0, 1315 jobs, `lower-profiles-build-1.log`. The log contains only the historical unused `inputs` warning from an older dependency.
- Imported public probes: 5 axiom reports and 5 fully explicit `@` signatures, exit 0 in `lower-profiles-public-1.log`.
- Imported integration probes: 3 axiom reports and 3 fully explicit `@` signatures, exit 0 in `lower-profiles-kernels-3.log`.
- The final direct public and integration logs contain no errors, warnings, or sorryAx. Reports use only the existing foundational axioms propext, Classical.choice, and Quot.sound.

The integration checks do more than restate endpoints. `two_operand_target` constructs the first-seeded Target and its ordered Reads from two actual Operand receipts and the query at their exact returned state. `warm_force` constructs a literal hit receipt from existing causal slot history; checked state, Merge memo, and global bundle are identical. `serial_leaf` uses the first actual Leaf's returned readiness, stores, and domain as the second actual Leaf's inputs. It derives the final bound against the original input.

The kernels verify concrete supplied component receipts. They do not assert initial-only completion. No future universal callback, profile, capacity, or result-law premise occurs. The production endpoint likewise verifies supplied actual reads and receipts. The remaining producer chain is in `lower-profiles-next-chain.md`.

Kernel attempt 1 failed on a namespace alias and graph-index inference. Attempt 2 fixed those indices but found an unavailable utility import and an unused existential binder. Both failed source copies and logs remain. Attempt 3 uses direct transitivity of the actual height inequalities and an explicitly unused proof binder. Production source did not change during these corrections.
