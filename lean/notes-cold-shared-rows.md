# Stateful cold shared-row execution

Checkpoints: `49498845`, `4601cf85`, and `f425e2b6`, upstream `f59c198d`, 2026-10-14.

`SourceColdSharedRows.collect` models the actual `reachable` worklist in
`cfta/src/Data/CFTA/Interned.hs`. Each first read calls the actual modeled
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

## Exact cold output language

`SourceColdSharedRowsMeaning.Trace.meaning` derives each actual row's exact
language equation in the final cache. `edge_stable` transports all ordered
child runs and full guards through later physical growth. It uses the checked
finite-exposure language transport for the root and each resident child.

`SourceColdSharedRowsLanguage.Trace.language_exact` derives the output graph
from the actual completed map. Canonical readback identifies each stored row's
original root. Closed child provenance and output declarations support
induction on finite terms. No fixed input heap or warmup is assumed.

`SourceColdSharedRowsTable.Trace.table_correct` derives the complete finite map
domain, ascending-key native readback, stable executable bounds, and original
guarded language. The table retains the empty-root special case.
`Trace.sized` composes exact distinct node-count classes, finite class
evaluation, distinct size-order prefixes, bounded coverage, and both inverses.

## Termination without a supplied trace

`SourceColdUnfoldBudget` counts unfinished source unfoldings in the actual
initial complete-record inventory. Non-Mu records are already settled. No
new Mu record is introduced by prepared stored substitution. Each completed
Mu unfolding replays without allocation through later cache growth.

The remaining budget cannot increase. Settling any unfinished inventory member
strictly reduces it. `SourceColdReaderBudget.nodeEdges_unchanged` proves that a
completed row read with unchanged budget retains the identical cache. It
includes repeated Mu requests inside ordered union closures.

`SourceColdSharedRowsTermination.complete` uses three lexicographic measures:
unfinished unfoldings, unvisited issued identities, and pending-list length.
A new row either reduces the first measure or retains the cache and reduces
the second. Known and empty values reduce the third.
`cold_finite` derives a completed actual trace and stable finite outer/read
bounds for every available closed root in a prepared cache. No `Ready` cache,
fixed heap, prior warmup, or supplied completed trace remains a premise.

## Actual construction and public queries

`SourceFirstOrderColdSized.source_rows` derives repaired empty-cache
construction, finite actual cold traversal, exact cache histories, the finite
returned table, and original guarded language. `source_sized` gives every
reference Sized law without warmup or a supplied trace. The construction body
can contain arbitrary finite trees and unions but no nested binder request.

`SourceColdSharedRowsSizedNative.sizedTable` preserves every raw transition,
constraint, child list, and row order. `Trace.native_correct` proves that native
dispatch uses the actual original canonical reference API. It includes exact
physical guarded membership, finite class derivations, distinct size order,
complete coverage, and both signed inverse laws. Validation and active equality
constraints remain explicit. Existing raw dispatch equality retains all errors.

`SourceColdSharedRowsSizedLiquid.Trace.liquid_correct` connects actual encoded
solver-decided folds to the original physical graph under independent ambient
logical meaning. It retains the canonical bounded sequence, finite classes,
distinct size order, bounded coverage, and both signed inverses. Finite external
attempts give finite outcomes, including Unknown and unchanged failures.
External response correctness and completion remain explicit contracts.

## Remaining obligations

The cold traversal theorem requires `Prepared`: each stored Mu body introduces
no dynamic binder request during substitution. Arbitrarily deep closed nested
Mu leaves are allowed. General source syntax can contain open nested binders;
deriving its preparation or a larger finite-execution invariant remains open.
The first-order source theorem derives preparation instead of assuming it.

Next connect native cyclic intersection construction and its product rows to
this cold adapter. Preserve exact constructor and memo effects. Completed plain
intersection does not prove pending recursive memo publication or the general
cyclic product-row result. General nested constructor/depth and equality work
remain secondary targets. Preserved counterexamples still refute strict generic
depth/head-rank shortcuts and saturated merge monotonicity.

The concrete product interface is
`SourceCyclicRowsNativeGate.ProductReadback.members` and `.rejected`.
Derive these from the actual `intersectOpen` branches in
`cfta/src/Data/CFTA/Interned/Operations.hs`. Retain `maybeMu`, open-domain
environments, recursive memo publication, and child effects. Do not assume
another row or language contract to use the existing `product_exact` theorem.

The older warmup result in [notes-first-order-shared-rows.md](notes-first-order-shared-rows.md)
remains valid. No theorem identifies warmup and cold allocation order or their
raw tables. The new cold proofs follow the actual source order directly.

Concrete Haskell containers, lazy evaluation, machine resources, external
solver/PRNG behavior, and verified extraction remain separate boundaries.

## Validation

The aggregate Lean 4.34.1 build passes 1,204 jobs and checks dependencies of
40,032 theorems. Only `propext`, `Classical.choice`, and `Quot.sound` are
permitted. All completed modules are in `MicroCFTA/Audit.lean`.
Log: `/tmp/mcfta-cold-complete-20261014-audit.log`.
No Haskell source or production tests changed.
