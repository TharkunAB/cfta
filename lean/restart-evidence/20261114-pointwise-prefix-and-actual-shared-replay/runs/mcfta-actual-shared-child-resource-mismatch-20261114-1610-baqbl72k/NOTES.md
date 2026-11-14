# Actual shared child resource target and first replay mismatch

Status: MARKED TARGETS ONLY. No proof implementation or patch is supplied.
No target is added as an axiom or as a premise of another theorem.

The actual eager worker uses SharedSelectedContinuations.ChildDispatch.run.
SharedEagerReservation.fallback_complete_resources_cps calls that namespace's
complete_with_fragments_resources in SourcePruningEnumerationSharedChildResources.lean.
The marked observed-resource target preserves every initial parameter and resource field
of that actual producer. It fixes the actual supplied raw row, caller, queries, outer core,
waiting state and Some cache. It covers both raw=[] and a successful singleton.
Only the producer's internal final memo, inventory and root function remain existential.
No future observation or resource provider is supplied.

The original lower producer requires Context, Safe, Roots, canonical waiting counts,
native index flags, PendingRealized, bounded/pending bucket inputs, available closed input,
allocation Fits, the original mixed Reserved schedule and annotation Heap.
The eager wrapper derives its structural inputs from its original Packet.
The lower producer does not separately take IncomingAvoid or mass parameters.
No original outer Packet, IncomingAvoid, mass or reservation clause is changed here.

First mismatch:
- Existing SourcePruningEnumerationChildDispatch.run_some_stable is about
  SourcePruningEnumerationChildDispatch.run, from the legacy child module.
- The actual resource producer is about
  SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run.
- Their terminal branches call CachedTerminalAdapter.run and SharedCachedTerminal.run,
  respectively. Their error types also contain different conjunction-worker observations.
- The shared terminal fold uses SharedDispatch and SharedEnabledEmpty.check.
  The latter calls SourceCurrentAllocatedSharedConjunctionWorker.call after the descendant memo.
- The legacy terminal chain uses the separate allocated conjunction worker.

These operations are separate definitions. The inspected replay theorem is not directly applicable.
This is not a proof that their successful payloads differ and is not an implementation defect claim.
No legacy resource theorem or successful-observation equality is substituted for the actual shared run.

The minimum top-level missing replay target is recorded separately with the exact Shared run.
Once that law is proved, compare the observed small call with the actual eventual producer at
r+r0, n+n0, p+p0, h+h0, k+k0. Use the producer at its own shifted representative/native/index
bounds and the same larger p/h. Equality of the full successful observation identifies raw,
afterCaller, savedQueries, outer core, waiting and the Some cache. Transfer every resource field
without changing an actual reached state. The empty row must remain covered in that comparison.

Root has separately identified actual shared conjunction call_done_stable at a fixed semantic
budget as a possible kernel producer. That is a new lead, not a proof of the marked child law.
Do not duplicate a full child/terminal replay family before checking this actual producer.

Every-common-budget stopped partial-output history and the full finite common original-root
witness, typing, LPO, language, stream, count, weight, rank and compiled-Haskell scope remain open.
No compiler, Lake, Nix, heavy job, Git, board, live edit or child agent was used.
