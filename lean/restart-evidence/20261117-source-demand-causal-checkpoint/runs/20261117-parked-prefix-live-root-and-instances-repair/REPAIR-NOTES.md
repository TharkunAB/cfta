# Minimal dependency and instance-retention repair

Status: **UNCOMPILED**. Preserve the original packet and strict failure log unchanged. Root owns all compilation and normal Source work.

The emitted QName was correct, but its defining module was absent from the local import closure. `SourcePruningEnumerationSharedPreparedLiveRoot.lean:31` defines `SourcePruningEnumerationSharedPreparedRecursive.emitted`. Adding that one ordinary import also permits the existing explicit open to resolve Output and emitted together. The repaired module adds no resource-owner dependency.

The first theorem now explicitly retains its two existing equality-instance parameters in underscore-named local values. The theorem previously auto-included these same Symbol and Node parameters, as the original printed declaration confirms. No parameter is added, omitted, strengthened or weakened. The other two proofs are byte-exact. No linter or checking option is disabled or raised.

The three full local public headers, probes, full OPEN header, OPEN definitions and OPEN preamble are byte-exact. Removing only the added import and the two local value lines reconstructs the entire failed raw module byte-for-byte. The static comparison records that check. This is not proof credit; the whole new module must pass Root's strict check.
