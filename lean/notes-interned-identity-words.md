# Machine identities and allocation lifetime

`InternedIdentityWords` models the counter in
`Data.CFTA.Interned.Cache.nextId`. The counter starts at zero. Each atomic
fetch-and-add returns the previous signed machine word. The proof counter
records the number of draws with an unbounded natural number.

`counter_exact` derives the stored word after every draw. `fresh_within_period`
proves that all draws before one full word period have distinct identities.
This includes negative identities after the signed boundary. Allocation order
agrees with signed identity order only before that boundary.

`finite_trace_distinct` derives a duplicate-free finite allocation trace.
`interleaved_fresh` permits interleaved callers with distinct draw ordinals.
The atomic primitive must supply those distinct ordinals. Its runtime
linearizability is an external contract.

`full_wrap` proves that a complete word period repeats identity zero.
`not_unconditionally_fresh` therefore rejects an unlimited freshness claim
for this finite-word supply. The source has no overflow check. This is an
allocation-lifetime boundary, not a reproduced practical failure. No source
change is made. Proofs that use globally fresh interned identities require
the finite lifetime bound and the runtime atomicity contract.

The word model uses one sign bit in addition to its `bits` parameter. The
concrete GHC representation and atomic operation remain source interfaces.
Validation uses the pinned Lean build and the aggregate axiom audit.
