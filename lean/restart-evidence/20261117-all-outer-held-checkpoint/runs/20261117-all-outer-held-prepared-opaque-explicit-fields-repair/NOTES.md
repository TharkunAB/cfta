Status: FROZEN UNCOMPILED annotation repair. Preserve the original draft and full failed62297 log.

The first failure occurs in the header's PreparedHistoryAt.opaque application.
Lean generalizes the mode match over completedCaller and preparation. The old
application leaves completedCaller unresolved until a later argument. The repair
supplies all existing constructor fields explicitly in that header application
and the final HeldPreparedHistoryAt.opaque proof term. It adds no data or premise.

The header is NOT byte-exact. The original93d4484f header is retained verbatim in
ORIGINAL-PRIVATE-HEADER.lean.txt. Every binder and premise is byte-exact. The result
uses the same constructor, existing fields, observations, suffix and index, now
with explicit field arguments. The conclusion contract does not change.
The proof body outside its final constructor application is byte-exact.
The shared5e4832 depth predicate and full public9374 target remain unchanged.

No proof or runtime limit, linter setting, resource input, budget, Canonical
premise, future Packet or history supplier changes. No compiler or Source edit.
