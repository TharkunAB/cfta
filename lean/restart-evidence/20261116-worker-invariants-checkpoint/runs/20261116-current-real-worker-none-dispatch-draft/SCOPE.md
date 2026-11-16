UNCOMPILED. This is the actual shared native dispatch writer case.
The literal action and exact successful singleton are retained. No future core,
model, Packet or ProperState fact is supplied. The only initial semantic fact is
NoneBucketsEmpty. The proof follows the checked existing dispatcher case split.

The new local assimilation proof uses the actual optional-handle origin. A new
None handle implies that both source slots had None handles before assimilation.
Their two old buckets are empty by the initial invariant. Some-handle native
query outcomes can never introduce a None bucket. The exact native query fuel,
enabled-check fuel and fourth-cache fuel remain unchanged on every branch.

The public dependency SharedEagerNoneBuckets is a frozen UNCOMPILED candidate at
this writing. This packet has no proof credit. It does not prove the full worker
or any history for the accepted source. It is a concrete necessary writer leaf.
