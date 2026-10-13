# Stateful cold shared-row execution

Checkpoint: `49498845`, upstream `f59c198d`, 2026-10-14.

`SourceColdSharedRows.collect` models the actual `reachable` worklist in
`microcfta/src/Data/CFTA/Interned.hs`. Each first read calls the actual modeled
`nodeEdges`, stores its ordered physical edges at the canonical identity, and
queues those edges' child values before the remaining work. The next step
uses the read's returned cache. Known identities retain their first row.
Empty values require no map entry. Closed inputs exclude unresolved values.

Outer traversal fuel and inner row-read fuel remain separate. Unresolved
references, pending construction, and exhausted proof bounds are distinct
outcomes. Each outcome retains its exact returned cache. The executor does
not assume a fixed heap, a prepared `Ready` cache, or a supplied finite output
identity domain. Per-record source reads still require `Prepared` for the
general completion and preservation theorems.

`Trace` records actual successful reads, their fuel, intermediate caches,
first-write insertions, and ordered child queues. `Trace.correct` proves cache
facts, structural preparation, physical growth, issued-map extension, absence
of new Mu records, first-row preservation, and resident closed child payloads.
`read_closed_of_done` proves that any successful sufficient read bound has
closed children. It compares the exact stable read witnesses.

`SourceColdSharedRowsExecution.collect_trace` derives the complete trace from
a successful executable run. `Trace.finite` proves the converse with a finite
uniform pair of outer/read bounds. Every larger pair returns the same map and
the identical final cache. No cache effect is discarded by this correspondence.

`Trace.extends` preserves all earlier map entries without cache premises.
`Trace.pending_done` declares each initial nonempty pending identity.
`Trace.closed` declares every nonempty child of every new row. Its premise
only concerns pre-existing rows. It is vacuous for the initial empty map.
`Trace.discovery` derives a finite distinct list of newly discovered keys,
disjoint from the initial map. These keys describe the exact output domain
in addition to the initial domain. This is a domain theorem; it does not assert
an order theorem for the chosen key list.

## Remaining obligations

These theorems do not derive a completed trace for every closed input.
Finite execution is proved for each finite trace. General cold traversal
termination remains open. Do not describe it as proved from the trace bound.

The next bounded target is final-table language correspondence:

1. Retain the exact language equation of each actual row read.
2. Transport that equation through later cache growth. Use
   `MergedColdGraphTransport.accepts_stable` for the original root and each
   resident edge child. Keep full guards and ordered child relations.
3. Use `Trace.correct`, `Trace.pending_done`, `Trace.closed`, and
   `Trace.discovery` to derive the finite final shared graph and its exact
   original physical language. The output heap must be derived from the trace.
4. Compose the returned table with the existing Sized laws. Then derive
   unconditional cold-walk termination and connect native cyclic product rows.

The first-order warmup result in [notes-first-order-shared-rows.md](notes-first-order-shared-rows.md)
remains separate. Native cold traversal does not run that warmup. Do not
identify their allocation orders or raw tables. A termination proof can track
completed Mu unfoldings and remaining initial Mu identities. It must account
for reads repeated inside union closures. Preserved counterexamples refute
strict generic depth/head-rank shortcuts and saturated merge monotonicity.

Concrete Haskell containers, lazy evaluation, machine resources, external
solver/PRNG behavior, and verified extraction remain separate boundaries.

## Validation

The aggregate Lean 4.34.1 build passes 1,195 jobs and checks dependencies of
39,965 theorems. Only `propext`, `Classical.choice`, and `Quot.sound` are
permitted. Both modules are in `MicroCFTA/Audit.lean`.
Log: `/tmp/mcfta-cold-shared-20261014-audit.log`.
No Haskell source or production tests changed.
