# Pending reservations through full nested execution

`InternedNestedPendingPreservation` proves that arbitrary source syntax
cannot complete an already pending ancestor record. The proof includes
all node, edge, union, raw Mu, and smart Mu constructors. It covers both
successful and pending outcomes.

`request_preserves_pending` follows the actual lookup and reservation.
A request for the same incomplete key stops. A different request can
write only its own record. Ordinary constructor work cannot write Mu
records. `build_preserves_pending`, `buildMany_preserves_pending`, and
`buildEdges_preserves_pending` compose these facts through the complete
source schedule.

The theorem requires valid initial caches and the exact existing pending
slot. It does not require a successful execution, a stable callback key,
or a restriction on source syntax. It does not prove that the initial
empty-cache execution always completes.
