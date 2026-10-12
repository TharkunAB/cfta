# Full-source provenance of a possible pending alias

`InternedPendingOrigins.Origin` records the actual state before a missing
Mu lookup, its two complete available probes, and its reserved canonical
entry. Constructor effects preserve the reservation and the earlier probe
records. `request_certified` adds an origin at the actual miss branch. A
pending hit obtains its origin from the current source pending-key coverage.

`InternedNestedPendingOrigin.build_certified` derives this property for all
finite nested syntax. The proof follows ordinary children, edge interning,
both binder probes, fresh callbacks, cache hits, and record completion.
Complete outcomes retain coverage and origins for the remaining pending
keys. Pending outcomes retain the actual origin of the failed key.
`closed_pending_origin` starts with empty caches and no pending assumptions.
It does not require any marked, retained, independent, or erased-body source
condition.

`InternedPendingProbeAbsence.closed_pending_fresh_absent` narrows any
hypothetical pending result. It supplies an earlier state and an identity
that was unused there but is now issued under the pending key. Both complete
original probes omit that fresh name, as derived from their earlier issued
reference provenance. Every resident probe pair with the pending key has
the same immutable records. Therefore both probes of any such alias omit
the name too.

This theorem does not prove that pending readback occurs or that all source
execution completes. It proves that the remaining possible failure must
use an ignored or normalized-away fresh dependency. The actual reservation,
probe availability, canonical residency, and fresh-name absence are now
derived for arbitrary source syntax. General completion still requires
earlier-request replay for that absent-name case across changed nested
local identities.

A temporary executable-model diagnostic changed the depth sentinel to a
genuinely reserved fresh reference. Among 139836 completed terms, it found
no changed canonical result when the new result omitted the fresh name.
It skipped 725 terms after a resource limit. This supports investigation of
the replay statement but is not a source implementation check or a proof.
