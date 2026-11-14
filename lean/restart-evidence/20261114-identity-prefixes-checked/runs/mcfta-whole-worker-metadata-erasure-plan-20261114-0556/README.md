# Exact metadata erasure for the existing eager worker

Created on 2026-11-14 at 06:00 CET. The new Lean code is uncompiled. The whole-worker theorem is a target interface, not a proved result.

`whole-worker-header.lean.txt` states the requested theorem. Both sides call the same actual `runEagerWithNarrow` with identity narrowing, templates `[]`, stop `none`, and order `(fun _ _ => none)`. They use the same graph, `checkEmpty`, `edgesOf`, work fuel, recursive fuel, caller, full query memos, and cache. One side receives arbitrary `Metadata Typing`. The other receives arbitrary `Metadata Unit`. Their complete results must agree after metadata erasure.

## Projection draft

The candidate module reuses the public `eraseMetadata` and `erasePrefix`. It adds five pure projections into existing datatypes:

| Projection | Exact retained fields |
| --- | --- |
| `eraseOutput` | Metadata option constructor, cache, caller, full queries |
| `eraseFailure` | Every failure constructor and raw hole ID; exhausted cache; selected prefix through the existing `erasePrefix`; callback errors, Boolean, Core, row order and duplicates; full preparation including a fault heap; processed alternative receipts; edge or continuation receipt and endpoint; recursive stop reason through the same map |
| `eraseResult` | Complete versus stopped, output order and duplicates, complete caller and queries, stopped optional endpoint |
| `eraseStop` | Edge versus continuation, exact receipt or optional receipt, exact endpoint or optional endpoint |
| `eraseFold` | Complete versus stopped, processed receipts in order, output order and duplicates, caller and queries, complete stop context |

`eraseStop` and `eraseFold` expose the maps needed to state transport through the existing continuation fold. They add no operational worker. The direct nested `eraseFailure` patterns recurse only on the existing continuation failure. No receipt or preparation is reconstructed from an approximation.

## Existing interfaces checked

The shared `NativeContinuations.HookResult`, `Stop`, and `Result` definitions contain no map operation. The repository search found no map for these types. The only `mapResult` name found belongs to `SourceSizedLiquidProgram` and is unrelated.

`SourcePruningEnumerationNativeContinuationCompletedCongruence.run_complete_congr` uses the nonshared receipt family. It compares the same `Output` and `Reason` types and assumes a completed source scan. `SourcePruningEnumerationSelectedContinuationCompletedCongruence` keeps those restrictions. They cannot supply an equality across the two metadata types or cover a stopped prefix.

The private `SharedEagerScalarObservers.scan_congr` and `SharedEagerFrontierResources.children_congr` also compare the same result types. Their structural proofs are useful templates. Their statements do not transport a projection across the result type.

## Concrete proof draft

The candidate contains five local theorem drafts:

- `eraseFailure_alternatives` relates the nested failure map to `eraseStop`.
- `finish_erasure` preserves the actual conversion from a fold into the recursive result. It keeps the alternative failure and its endpoint.
- `scan_erasure` moves `eraseFold` through the actual shared `scan`. It has no agreement, readiness, completion, model, or productivity premise. It covers stopped visitor results and stopped sibling suffixes. Its proof uses list induction and `List.map_append`.
- `receipt_erasure` moves the map through the actual single-receipt continuation. It retains missing receipts, rejected edges, finalization stops, child stops, stopped hooks, and all endpoints.
- `continue_empty_exact` expands the actual Left callback for templates `[]`. It returns the same caller and query memos, and the recursive call receives `frame before.core before`. Metadata changes only through `updatedTypes`. The induction hypothesis can quantify over both resulting metadata records.

These are proof drafts. No compiler ran. `proof-plan.md` gives the remaining proof dependencies. `obligations.lean.txt` gives exact headers for eager-child transport, prepared transport, the recursive theorem, and the final theorem. `final-entry-proof.lean.txt` gives the final wrapper proof after the recursive theorem is established. It does not declare that recursive theorem as an axiom.

## Evidence and scope

`source-pins.json` records hashes for fifteen inspected source files. `source-excerpts/` freezes only the relevant definitions and earlier congruence statements. The public prefix module has SHA-256 `1d3d08ba63ede9939bb7ef2457a53912670e5c15147cab13956fc1fc4f204838`, matching the reported integrated prefix checkpoint. The prior approved plan files remain unchanged.

`candidate.patch` adds only the projection and local-transport module. GNU patch adds it with zero fuzz to an empty temporary tree and reproduces the exact candidate bytes. The inverse patch removes the file with zero fuzz. These checks establish mechanical replay, not Lean elaboration.

No compiler, runtime probe, live source edit, Haskell edit, Git operation, or message board write ran. The draft adds no datatype, provider, operational worker, or callback hook. It does not establish an accepted output, adequate fuel, finite completion, source/Haskell correspondence, or Haskell runtime behavior.
