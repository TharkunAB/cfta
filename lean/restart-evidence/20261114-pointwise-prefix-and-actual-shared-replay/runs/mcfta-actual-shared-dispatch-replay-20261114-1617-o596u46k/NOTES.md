# Actual shared dispatcher replay

Status: UNCOMPILED candidate. Root owns strict checking and publication.
Add only SourcePruningEnumerationSharedDispatchStability.lean.
No operational definition or existing declaration changes.

Two declarations are added in SourcePruningEnumerationSharedDispatch:
- afterQuery_ok_stable retains the exact optional enumeration action, returned full caller,
  and query memo at independently larger p and h.
- dispatch_ok_stable retains those same fields at independently larger native, p and h bounds.
Neither theorem takes Context, Ready, resource, successful-future-result or callback premises.
The only premises are the actual successful observation and the three relevant bound comparisons.
An optional action may be none. A present action is retained as the exact monadic function.
Thus its result at every supplied enumeration core stays the same.

The afterQuery proof follows the actual shared enabled outcome:
- checkEmpty=false is independent of p/h.
- A skipped outcome uses Root's checked check_skipped_at_any_bounds.
- A performed successful shared call uses Root's checked check_performed_done_stable.
- A performed failed call has no completed verdict and contradicts an ok afterQuery observation.
The performed-success leaf retains answer, checked state, fourth memo, private snapshot and query memo.
The fixed semantic tuple budget is currentTupleBudget. It does not change with p/h or work fuel.

The dispatch proof follows the actual source/target lookup branches.
Only the native-query branch depends on nativeFuel.
SourceEqualityNativeDemand.done_stable replays the exact query and entire queried checked state.
The shared enabled call then receives that identical query and checked state, the original fourth memo,
and the same query memo at larger p/h. No native alignment field or action is replaced.
The structural branch proof follows the existing dispatcher proof, but unqualified dispatch and
its afterQuery_ok_stable resolve in the actual SharedDispatch namespace.
No legacy dispatcher or enabled-empty replay theorem is invoked.

The canonical shared leaf import is SourcePruningEnumerationSharedEnabledEmptyStability.
Root reported its frozen source strict PASS at16:15 CET:
/tmp/mcfta-shared-enabled-check-replay-20261114-1612/SourcePruningEnumerationSharedEnabledEmptyStability.lean.
Its exact bytes are retained as a review text file. No namespace overlay is created.
STATIC-CHECKS.json records whether the canonical live import was visible at freeze time.
Static import analysis uses that exact checked source as text and finds no local cycle.

The two public theorem header shapes and native branch proof were compared with the existing
stable dispatcher proof. The names now refer to the actual shared operations.
Static checks give no Lean elaboration or axiom-closure credit for this new module.
No compiler, Lake, Nix, heavy job, live edit, Git, board or child agent was used.

This is one dispatch producer only. Actual shared terminal/fold/cache/child replay is still open.
The marked shared child observed-resource target remains unproved in
/tmp/mcfta-actual-shared-child-resource-mismatch-20261114-1610-baqbl72k.
Both empty rejection and singleton Some-cache child observations still require the actual shared lift.
All-budget worker stopped partial-output history remains open.
One finite common accepted original-root term and assignment, parked backward recompletion,
and every original typing, LPO, language, stream, count, weight, rank and compiled-Haskell clause stay open.
