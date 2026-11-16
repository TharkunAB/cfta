UNCOMPILED counterexample packet. Root owns strict checking.

The missing implication is false for an abstract current Packet. The cache has
one allocated root. Its pending payload has node=none and one valid path[0]
obligation that names the same root. Its exact waiting count at0 is1. Native
candidate returns some false for every node=none payload. The candidate list is
empty, so noStop restart reports done. Packet's Safe, PendingReferences,
CacheValid and Stratified fields do not include the missing ProperState fact.
The native Context is unchanged and independent of this fabricated enum cache.
This does not establish that an accepted original source can reach this cache.
No Haskell defect is claimed.

Exact existing producer for histories that it covers:
1. SourcePruningEnumerationRecursive.initial_packet_proper produces the actual
   original startup Packet AND ProperState. It retains the full original startup.
2. SourcePruningEnumerationRecursive.ResourceHistory.proper_output transports
   that property through its retained actual operation/entry/head/callback path.
3. At that output, `proper (.unenumerated none scs)
   (List.mem_of_getElem? stored)` has type scs=[]. No done premise is needed.
4. run_finite_complete_resources_with_history supplies those histories for the
   older SourcePruningEnumerationRecursive.run at its derived stable bounds.
   ResourceHistory.forget targets Recursive.OutputHistory and its exact
   Recursive.resume continuation. It cannot be substituted for the new
   SharedPreparedRecursiveChildPolicy.runWithNarrow eager worker, nor used as
   a SAME-original-workFuel claim outside its stated stable family.

Actual source origin inspection:
- EnumerationState.allocated always creates .unenumerated node [].
- SharedDispatch.dispatch_proper proves a merged missing handle can arise only
  from two missing old handles; their empty buckets then append to[].
- SelectedPrefixProper.prepared_nonempty_proper stores some encoded newHandle.
- checkRepeated_proper parks some handle with an empty bucket.
- Finalization writes .enumerated, not a missing-domain pending payload.
- Child visitor allocation of unrestricted holes uses node=none,scs=[].
- Real narrowing changes a native handle; it does not invent node=None with paths.
These facts show no concrete source path to the fabricated payload. A proof for
ALL eager real emitted endpoints has not been identified in the public API.
The new original-budget resource theorem gives Packet, not ProperState.

Smallest remaining source producer:
Transport only `forall uv scs, core.values[uv]?=some(.unenumerated none scs)
 -> scs=[]` from the actual initial root through the literal eager real worker.
Use the checked actual task/work and recursive-depth inductions at the original
workFuel, with original captured caches and all emitted prefixes. This property
needs fewer facts than all ProperState. The existing primitive proofs above are
reusable; the actual task/worker composition is the missing link. No future
ProperState, TupleInputs, callback law or endpoint resource supplier should be
added to the original full completion goal.

The independent pending-domain assignment theorem is local model construction.
This audit concerns its missing actual None-bucket producer. Historical buckets,
retained residual guards and original-root acceptance remain separate.
