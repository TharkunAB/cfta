# Closed-root physical enter factor

Status: FROZEN UNCOMPILED candidate. Root owns checks and normal Source integration. No compiler was run. This is a physical interface bridge, not the global retained-cell semantic producer.

The new theorem reuses the private `trace_closed` proof in the same Source owner. It exposes the exact full closed operands and identity pair of a literal enter reached from the original closed empty-domain root. It retains the original Checked start, intermediate reader, query control, prefix count, continuation, and singleton-key observation. It changes no runtime or supplied fuel.

The existing `stored_dispatch_enter_closed_operands` obtains `rootClosed` from two pending native lookups. Its remaining proof is the complete proof body here. Only the root start expression changes from `caller.checked` to the explicit `before`. The private trace invariant and empty-root domain ancestry law are reused directly. The old theorem, all old proof bytes, and all old headers remain unchanged.

`SharedIncomingQueryHistory.prepared_incoming_success_query_history` already derives incoming/old closedness from the actual parent Packet, one actual own preparation, and the same selected staged position. Its staged operand need not have a pending-slot lookup. This factor removes that narrow two-slot requirement at the physical enter layer. The later full-operand/canonical-entry/warm-entry chain would still need to use this interface.

The theorem assumes only honest PAST physical and root-operand facts, plus the actual prefix and key observation to be analyzed. It assumes no future cache, source family, Profile, Result, OnlyU, assignment, callback, or semantic law. It does not produce a past authentic source entry for a retained returned cell. That chronology gap remains as recorded in the separate actual-warm-query-entry-attachment audit.

## Layout

Append `APPEND.lean.txt` to `SourceCurrentAllocatedNativeSourceEmptyEnterOperands.lean` in the same file. Do not import that owner into a new standalone module and try to access its private `trace_closed` constant. No new import is required. Preserve the entire pinned original owner as an exact prefix. Append `PROBES.lean.txt` only to the check input. Do not include probes in the normal source hash.

Use default proof limits. There is no heartbeat override, new datatype, new runtime, or additional proof framework. The FIRST header is byte-exact in APPEND. All old Source files remain unchanged by this packet.

The full original accepted-root finite completion, every historical obligation under one assignment, native inhabitance, and Type/Marker consistency remain open.
