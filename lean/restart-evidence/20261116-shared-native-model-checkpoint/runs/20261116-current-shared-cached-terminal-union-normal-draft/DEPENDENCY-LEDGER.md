# Source dependencies and remaining worker boundary

| Actual source declaration | Pinned source position | Proof use |
| --- | --- | --- |
| SharedCachedTerminal.rawFold | SourcePruningEnumerationSharedCachedTerminal.lean:47 | Induction over the unchanged ordered recorded sources. |
| SharedCachedTerminal.fold_erase | Same source:128 | Exact cached/raw caller equality. |
| SharedCachedTerminal.raw | Same source:234 | Actual prefix, fold and incoming observations. |
| SharedCachedTerminal.erase | Same source:323 | Exact cached/full raw terminal caller equality. |
| SharedDispatchUnionNormal.dispatch_unionNormal | SourcePruningEnumerationSharedDispatchUnionNormal.lean:61 | All dispatcher outcomes. |
| SharedIncomingUnionNormal.run_unionNormal | SourcePruningEnumerationSharedIncomingUnionNormal.lean:32 | Separate actual shared incoming call after successful singleton fold. |

The next worker consumer is actual SharedSelectedContinuations.ChildDispatch.observe/run. Their terminal branches use these exact raw/run functions. Their other branches retain the caller. Beyond this boundary, the real child callbacks, list scans and recursive restart must carry the same normality through genuine smaller-task/depth induction. An arbitrary future callback preservation premise is not a completed worker proof. Resource correctness, heap extension and this normality property do not establish the full joint assignment.
