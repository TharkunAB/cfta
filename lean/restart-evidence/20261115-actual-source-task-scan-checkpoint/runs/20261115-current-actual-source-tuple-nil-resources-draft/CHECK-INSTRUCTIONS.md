# Same-file check

Status: UNCOMPILED. No proof credit.

Copy the pinned complete SourcePruningEnumerationSharedEagerReservation source as the compiler input. Append APPEND.lean. Append PROBES.lean.txt. Run the standard strict check on that combined source.

APPEND.lean has no imports. It uses existing private declarations in the same source file. It uses no private-name encoding or visibility change. The original source is not changed by this packet.

The header and probes were frozen before the proof. SOURCE-PINS.sha256 identifies the live base that was inspected. The full prepared scan, all original caller premises, the real-narrow objective, and the joint one-assignment objective remain unchanged.
