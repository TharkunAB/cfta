# Current source context

The two new theorems fix Typing to Unit and native width to bits + 2. Only
DecidableEq EdgeKey is in scope. They use the owner aliases and existing
ChildInputs, TupleInputs and Packet definitions without changes.

The literal own receipt has the actual current caller heap, current cache,
source bucket, row and staged list. The provenance proof reads the exact
returned cache and staged list from CachedOwn.complete. It explicitly types
the staged source projection before the map reduction. No EnumGuard meta is
introduced by an untyped local staged definition.

The outer current certificate supplies the Packet before inner preparation.
The preceding checked-if-accepted own-prefix helper supplies the outer and
inner certificates at the returned own cache. The first inner child certificate
then supplies its actual Post and reached Packet. Its current pending premise
provides protection for all currently enumerated roots. Original outer-root
protection requires the derived source bucket-avoidance fact.

The existing tuple_inputs_extend_current_head extends the inner prefix.
The new proof retains the outer prefix without appending the inner fragment
to the outer fragment list. It lifts only the old outer fragment bounds and
preserves their pending and separation facts at the actual reached cache.
This distinction is required for a later actual row-assembly operation.
