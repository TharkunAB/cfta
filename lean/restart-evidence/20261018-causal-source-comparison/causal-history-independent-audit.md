# Independent direct-history profile audit

Reviewed on 2026-10-18 at 20:40 CEST. `SourceCurrentCausalHistoryProfiles.lean` has SHA256 `78ac761edfd4a2575d92931f8b96488814d2bd1e15e29d103ecaf20c9017d8fc`.

No material issue was found. No Lean check or source edit was performed. The earlier full-source audit remains unchanged.

`history_heap` inducts directly on the supplied finite `NativeMuPublication.History`. It generalizes both the empty-table prefix and the initial payload heap before induction. The trans case extends the prefix forward with the exact first path. A retain step needs only NoNewMu because the target Correct predicate is state independent: each exact final Mu record already occurred before the effect. No readiness, table growth, or issued-name extension is inferred from this retain constructor.

For a publication, the Depth subtree derives its endpoint heap. The ordinary subtree then derives its heap. Reservation changes only nodes and leaves nodeRecords unchanged. The reserved-body subtree derives its heap. The proof constructs History empty event.afterBody by composing those exact callback prefixes and the reservation. It then calls the already proved conditional CausalSourceComparison.publication with the pre-installation heap and history. Only complete installs the proved candidate or retains an older winner. No premise about the current candidate is assumed to derive that candidate. Nested publications are earlier callback subtree results, including a nested earlier winner at the same key.

`heap reader history` discharges its initial heap at empty tables. It takes no extra Context argument, but every History.publication already retains its actual Publication.context and callback equations. History can overapproximate ordinary effects through NoNewMu; its conclusion is only the pure stored-payload contract. It does not prove physical validity or Ready for an arbitrary reader.

`compare` removes only the explicit old Correct heap from the original full source comparison. It keeps actual entry Contexts, Aliases, exact scoped profile/cut compatibility, completed calls, and both forward Grows. It obtains the reader heap from the exact history. `build_heap` similarly removes its initial supplied Correct heap while retaining the actual entry Context and empty-table history. These adapters do not make unrestricted arbitrary-cache fusion true.

This proof closes derivation of the assigned root-profile payload contract from the stated causal history. It is not an all-depth guard-language theorem, general traversal completion, or Haskell correspondence result. There are zero new checks or public pairs owned by this review.

## Pins

| File | Bytes | SHA256 |
| --- | ---: | --- |
| `lean/MicroCFTA/SourceCurrentCausalHistoryProfiles.lean` | 5545 | `78ac761edfd4a2575d92931f8b96488814d2bd1e15e29d103ecaf20c9017d8fc` |
| `lean/MicroCFTA/SourceCurrentCausalSourceComparison.lean` | 4699 | `1c56e9317225d392e27aad94f2f0d9ae4a49658f5c7d99009af046d14e831e8f` |
| `lean/MicroCFTA/SourceCurrentCausalPublicationProfile.lean` | 9832 | `ab2e17de3e8cb67c495a1ae01bcd9e4b180a3ae3bf3de1089ac1df1e595717df` |
| `lean/MicroCFTA/SourceCurrentCausalPublicationHeapInduction.lean` | 5160 | `038c9e9b5b2e7b47c45bf578a5ec2f7e8aa98285a999a893e81fe6e99bfdfe4b` |
| `lean/MicroCFTA/SourceCurrentPublicationHeapInduction.lean` | 6639 | `690392065b04a6b3e30a22279b058b8b88214d0ffa985e26d127f44ac3f6df9a` |
| `lean/MicroCFTA/SourceCurrentNativeMuPublication.lean` | 24007 | `e24184ee19ac4028a3e1604a82fc3cfea92f4b40d5a8490d08f02143b049efb2` |
| `lean/MicroCFTA/SourceCurrentStoredMuProfileContract.lean` | 4689 | `278c5d9942df52bc6ec7b9ac3d28b430340d3c8cf20050ae2a8f6d0fd00c9040` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-history-strict-1.json` | 780 | `06ceb3fae011434e20025d6a242c2e783f2873f39c38a517bd1bb768f4b346f3` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-history-strict-1.source.lean` | 5545 | `78ac761edfd4a2575d92931f8b96488814d2bd1e15e29d103ecaf20c9017d8fc` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-history-strict-1.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-history-strict-1.limits.json` | 90 | `408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-history-canonical-1.json` | 618 | `876e28762ed7bf0927f730b8f1fb22caec7ff8e1db924b85229ebc6617744419` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-history-canonical-1.log` | 114 | `9a227262817250f8950e89981db3038224b8860b19872950f808bc74bc370782` |
| `lean/restart-evidence/20261018-causal-source-comparison/causal-history-canonical-1.limits.json` | 90 | `408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3` |
