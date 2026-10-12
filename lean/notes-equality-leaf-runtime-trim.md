# Runtime-cache occurrence reconstruction

`EqualityLeafProjectionTrimExact.raw_pullback` removes the cache-padding
boundary for finite raw occurrence witnesses. It starts with a witness in
any coherent cache and an available identical complete value in the actual
runtime cache. It derives a trimmed witness that compiles without allocation
in the runtime cache. It needs no cache-growth relation between those caches.

Trimming removes dead original ancestor rows before it visits their
children. Every live original row occurs in the canonical parent record.
Its edge and child records are already resident in the runtime cache.
Surviving duplicate rows can remain. They use the same resident requests.
The complete parent record determines an exact node-cache hit.

`EqualityLeafProjectionTrim.progress` proves that trimming decreases the
occurrence weight unless the syntax is unchanged. `admissible` proves that
selected leaf endpoints stay admissible. The raw instance uses
`EqualityRawLeafPullback.represented_pullback` for admitted finite raw leaf
requests. No rejected sentinel request is introduced by those leaf witnesses.

Later proof preparation remains a proof step. It does not alter runtime
execution or supply the next runtime cache. These theorems reconstruct the
needed witness in the actual cache after that execution.
