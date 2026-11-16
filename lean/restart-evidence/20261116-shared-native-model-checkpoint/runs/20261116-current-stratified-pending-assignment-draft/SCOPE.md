UNCOMPILED finite current-state model only.

The theorem uses EnumerationAssignment.evaluateSlots at frontier+1 and the same
UnionFind roots and Stratified levels as stratified_assignment. Pending roots
use the one prescribed fallback. Expanded roots use the same fragment evaluator
and evaluateSlots_stable. A single assignment supplies all slots and UF aliases.
No assignment, model, arbitrary compatibility oracle or Discharged proof is given.

The only changed hypotheses are explicit current-slot facts. Each pending bucket
is empty. If its node field is some handle, its domain admits the same fallback.
The original node=none restriction is removed. This is not a producer for those
facts and must not replace a missing producer in the original top-level goal.

SourceSynthesisCurrentDonePendingTypes.done_pending_type_members proves empty
buckets and membership of every TypeIn choice in each graph-bearing done slot.
Instantiate language with NativeLanguage.handles on that exact endpoint heap.
One uniform TypeIn fallback is available through TypeIn.leaf for literal var1,
which is independent of the constructor catalog. The done theorem still needs
its stated endpoint Normal/UnionNormal/source growth/only-U producer facts.
Its conclusion covers some handles. The generic theorem separately requires
empty buckets at any node=none pending slot as well. No such fact is invented.

The conclusion covers the current representatives and the current value array.
It does not include state.obligations, guardsHold, removed historical suspended
buckets, arbitrary old path equations, native cache meaning, source-worker
acceptance or one accepted original-root completion. These obligations remain.
No Haskell behavior or correspondence claim is made.
