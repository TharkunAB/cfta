[2026-11-15 05:29 CET]

UNCOMPILED candidate. Root owns compilation and publication. This packet changes
no live Lean, Git, board or Haskell source. It writes no /tmp files.

The new public theorem is `observed_retained_protected_isolated_pending` in
`MicroCFTA.SourcePruningEnumerationSharedChildIsolation`. Its actual-call premise
retains the entire `ChildDispatch.Observation (bits + 2)`, including any result tag,
the reached caller, the query memo, the outer core and the waiting index. It also
retains the exact `some after` cache. The theorem concludes complete `Protected`
from the original before core to that cache core, and the same raw held root,
native handle and `IsolatedPending` there. Its past semantic premises are the
existing Safe, IsolatedPending, input-target bound and input Avoids facts.
No resource bound, future endpoint, future invariance or model is an input.
The original checkEmpty and r/n/p/h/k are unchanged at every call.

The proof reuses the published successful singleton observer. It does not copy
its terminal or preparation proof. It uses the existing all-result raw-fold
isolation proof through Root's visibility-only export. The two new private helpers
have concrete operational scope. `actual_fold_retained_core` proves that each
retained fold cache has its actual outer core. `actual_incoming_read_frame` proves
that each actual incoming read is the original core or an actual findRoot
compression frame. Both helpers inspect the real shared definitions.

The incoming empty case uses Root's checked and published
`IncomingCacheAdapter.adapt_empty_protected_isolated`. The actual adapt equation
produces the sentinel write and the old bucket. The proof derives the read
isolation, read-input avoidance and read protection from the actual compression
frame. The target inequality comes from the actual terminal prefix. It supplies
no old bucket, future protection or semantic model by premise.

Case ledger:

| Actual branch | Cache and proof |
| --- | --- |
| Empty incoming value | The source retains the original cache. |
| Nonterminal cached preparation returns no cache or unsupported rows | Retained-cache premise is impossible. |
| Nonterminal cached preparation returns empty rows | The source retains the original cache. |
| Nonterminal cached preparation returns a singleton | Erasure derives the exact successful shared call. The published observer applies. |
| Terminal prefix has no successful singleton | The source returns no cache. |
| Shared fold returns a native fault or no raw result | The source returns no cache. |
| Shared fold rejects with empty raw rows | The actual retained fold cache has the outer prefix core. Prefix protection and the public all-result fold isolation compose. |
| Shared fold has stopped or unsupported raw rows | Terminal.run returns no cache. |
| Successful fold loses its cache | The fallback incoming path retains no cache. |
| Incoming native fault or unsupported result | Terminal.run returns no cache. |
| Incoming adaptation retains an empty result | The actual read frame and actual empty-sentinel write preserve the complete class and isolation. |
| Incoming adaptation retains a singleton | The actual incoming call and adaptation reconstruct the exact successful child singleton. The published observer applies. |
| Other incoming raw shape | The checked adapt_retained_shape excludes retention. |

No accepted-source obstruction was found in these literal cases. This is a draft
of the all-retained theorem, not proof credit before Root's strict check.

This result covers retained child caches. It does not quantify a conclusion over
cache-none returns. It does not prove all source-task cases, captured sibling
restoration, a whole-history temporal DAG, or one finite assignment satisfying
all retained and historical removed paths, aliases, narrowed domains, fragments,
residuals and the same original emitted root. The full finite-witness goal stays
open. Root owns the preparation-input factor and later preparation composition;
this packet adds no preparation API.

The source hashes are in SOURCE-PINS.json. STATIC-CHECKS.json records only textual
and dependency checks. Probes.lean contains the public axiom probe. No compiler
was run for this packet.
