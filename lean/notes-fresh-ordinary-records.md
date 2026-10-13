# Source record invariants for repaired ordinary placeholders

Updated: 2026-10-13 16:48 CEST.

The repaired executor now derives its record invariants from actual source
execution. These proofs use `InternedFreshOrdinaryConstruction.build` and
the matching `InternedFreshOrdinaryFacts.callback`. They do not apply the old
fixed-depth callback semantics to the new schedule.

`InternedFreshOrdinaryFacts.build_verified` preserves canonical record
coherence, child availability, outgoing edge residency, record-table growth,
and issued-reference history. Ordered child and edge versions derive the
same facts. `closed_verified` starts from empty caches and needs no supplied
invariant. Both completed and pending outcomes satisfy the result.

`InternedFreshOrdinaryGrowth` derives validity and record growth from cache
validity alone. It needs no successful result or available-input premise.
`InternedFreshOrdinaryPending` proves that an already pending ancestor slot
remains without a completed record during any nested source computation.
Its `callback_pending` theorem uses the repaired callback. This preserves
an active slot; it does not exclude a nested readback at that slot.

`InternedFreshOrdinaryOrigins.Heap` records the actual construction history
of every complete recursive payload. An origin includes its expression,
lexical environment, initial facts, exact Depth callback, exact ordinary
callback at `ordinaryLevel depth`, missing reservation, and exact fresh-body
callback. `closed_origins` derives this heap for every closed source outcome.
It retains origins from computations whose returned edges are later removed.

`InternedFreshOrdinaryReadback.request_miss_record` proves that a completed
miss installs the actual fresh body together with the exact two requested
probes. The active-slot theorem excludes an intervening completion at that
key. `hit_probes` derives equality of the full stored and requested probes
from canonical identity, coherent records, and input availability.

`closed_stored_probes` combines the derived source origin with both matcher
fast paths. Depth readback returns the original Depth record. Ordinary
readback uses the level selected from that record and returns the original
ordinary record. The chosen name is absent from the Depth record's free
names. This theorem concerns the two stored-probe branches; it does not
assert substitution correctness for every other matcher argument.

All these results account for the effects of discarded children. None infers
that an ordinary name absent from a returned value was absent from discarded
computations. The earlier `InternedProducerPathBoundary` remains relevant.
The repaired Normal, profile heap, and free-name heap now have separate
full-execution proofs. See [profiles](notes-fresh-ordinary-profiles.md) and
[free names](notes-fresh-ordinary-free-names.md). General repaired no-pending
remains open.

The five new modules build with Lean 4.34.1. The readback target passes
194 jobs. The focused audit checks 8,130 theorem dependencies and permits
only `propext`, `Classical.choice`, and `Quot.sound`. The log is
`/tmp/mcfta-fresh-ordinary-record-audit.log`.
The original executor, counterexamples, and marked draft remain unchanged.
