# Actual shared raw and cached fold replay

Status: UNCOMPILED candidate. Root owns strict checking and publication.
Add only SourcePruningEnumerationSharedCachedFoldStability.lean.
It adds three public proofs in SourcePruningEnumerationSharedCachedTerminal.
No existing operation or declaration changes.

rawFold_ok_stable retains the entire raw option, reached caller, saved queries and outer core.
cachedAdapter_ok_stable retains the entire raw option, reached caller, saved queries and optional cache.
fold_ok_stable retains both the complete raw endpoint and optional cache.
Each theorem permits independently larger native, p and h bounds.
The actual outer ok observation and the three bound comparisons are the only premises.
There is no semantic invariant, future-result, callback or resource provider.

The result shape is Option Raw. It includes Some [] rejection and a literal successful singleton.
It also preserves other outer-ok raw observations and None without giving them completion semantics.
Some and None cache paths remain exact. No missing cache is replaced with a constructed cache.
The returned caller and query memo are retained even when the raw row list is empty.

The actual rawFold induction uses the checked SharedDispatch.dispatch_ok_stable.
The captured action is exactly the same function at the same core.
The pure cache adapter therefore receives the same reached heap, original cache, source, target and raw row.
It has no independent fuel parameter. No new adapter abstraction is added.
The cached fold recurses through the same recovered cache when Some is returned.
When the cache is absent, its actual rawFold tail is replayed and the absent cache stays absent.
The proof covers empty rows, singleton rows, optional absent rows and other raw stop forms directly.

Existing structural fold proofs supplied the case-analysis pattern.
The new theorem calls resolve only to actual SharedCachedTerminal and SharedDispatch operations.
No legacy fold, cached terminal, dispatcher or incoming replay law is substituted.
The existing pure CachedAdapter.adapt remains the actual operation used by the shared backend.

Root reported the unchanged SharedDispatchStability source strict PASS with two standard-axiom reports
at16:22 CET. Its source SHA is018bcf87ff68eb9f4586474aba257ea14fe400ed3e7310aec53fea378df4c635.
The canonical import is SourcePruningEnumerationSharedDispatchStability.
The exact dependency is retained as review text, not as a namespace overlay.
Static import analysis used that checked source text and found no local import cycle.

The pure terminal prefix already has run_singleton_stable at larger representative bounds.
The pure incoming cache adapter already has adapt_some_stable at larger index bounds.
The full shared terminal run also calls the actual SharedIncomingNode.run.
Its exact successful empty-or-singleton replay remains the next missing producer in this packet.
NEXT-ACTUAL-INCOMING-RUN-TARGET-UNPROVED.lean.txt records that actual operation and every reached field.
NEXT-ACTUAL-TERMINAL-RUN-TARGET-UNPROVED.lean.txt records the subsequent complete Some-cache target.
Neither marked target has a proof or becomes an assumption of these three theorems.
This packet does not claim actual shared child replay or the observed child resource transport yet.

No compiler, Lake, Nix, heavy job, Git, board, live edit or child agent was used.
Static checks do not establish Lean elaboration or axiom closure for the new proofs.
All-budget worker partial-output inclusion and one finite common accepted original-root term/assignment,
parked backward completion, typing, LPO, both language directions, stream behavior, count, weight,
rank and compiled-Haskell clauses stay open.
