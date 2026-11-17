# Captured invocation event helper for the held join

Status: FROZEN, UNCOMPILED.

The private header was frozen before the proof. The helper copies the existing private captured-event proof into the new join module. It uses the public invocation event-ledger producer and public authenticity theorem. No private declaration from the old module is referenced.

Eliminate the supplied actual callback invocation once. Use its selected trace to produce one event list. Prove authenticity for that same ledger. Retain the invocation's literal finalizer, false callback, local index, fragment, and endpoints. No ledger is selected from another nested trace or sibling branch.

Assembly order: shared preamble; shared definition and typeclass context as required by the core packet; HELPER.lean.txt; the core join proof; namespace end; appendable probes. The standalone normal-module copy contains this helper only. The helper has no dependency on OuterEntriesHeld and may occur before its definition. Do not add the preamble or typeclass context twice.

The helper has no Canonical, Total, resource, semantic, or future-provider input. The supplied invocation is an actual structural receipt. This proof does not establish a joint semantic model, target typing, or truth of all removed constraints.

The default proof limit remains in force. No maxHeartbeats option is added. No compiler was run. Normal Source and all existing packets remain unchanged.
