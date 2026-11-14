# Actual tuple prefix native reservation

Status: UNCOMPILED. Root owns compilation and publication.
The candidate appends three private proof drafts to the frozen 9608 source.
The entire base is a contiguous byte-exact prefix. All original marked
full-worker and prepared targets are preserved byte for byte.

The missing native admission relation is explicit. tupleReserved supplies the
complete ordered fallback reservation with count * (bound + 1) native entries.
The proof follows the fallback conjunct of the original nodeReserved predicate.
It composes reservations from the same seed through advance_add.
It does not compare numeric profiles from unrelated guard schedules.

identity_actual_tuple_prefix_costs proves a structural invariant for the three
current source context cases. The current seed is advance initialSeed consumed.
Consumed native queries are at most completedPrefix.length * (bound + 1).
The mass is at most initialMass + completedPrefix.length * bound.
The completed-prefix length plus the remaining-input length is staged.length.
Every remaining input is a member of the original staged input list.
The fallback constructor charges the actual bucket length plus one query.
The ordinary empty-row constructor consumes one input without a native query.

identity_actual_fallback_native_reservation combines that actual source
invariant with the original tupleReserved and staged length/bucket bounds.
It derives Reserved bits currentSeed (actualBucket.length + 1) at the literal
fallback callback entry. The theorem does not assume a reached reservation.
It assumes no ChildInputs, TupleInputs, callback result or future resources.

These three proof drafts close the precise native reservation sub-obligation
for the current restricted context family if Root checks them. They do not
prove current Packet, remaining-input resource validity, accumulated TupleInputs,
or the actual empty-tail callback resource conclusion. The captured base still
needs a Packet at the observed cached-own singleton from the original Packet.
Fallback and empty-row resource cases can then use the actual entry producers
and Root's forward tuple_inputs_extend_current_head composition helper.
The genuine same-workFuel smaller-depth IH remains necessary at the captured
worker callback. It is neither weakened nor replaced here.

General ordinary rows with children require a larger source-context induction
and the corresponding nested reservation relation. This restricted fallback
cost formula must not be reused for those unrepresented cases. General cons,
scan resources, the full worker and the common finite original-root witness
remain OPEN. Root reports closed/mixed generated-Type proved/public at 89b16012b.
No Haskell defect was found. No Haskell or FINDINGS file changed.
No compiler, live-source, Git, board or tmp write occurred.
The clear-writing checks were applied to these notes.
