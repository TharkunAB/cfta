# Record coherence from empty-cache construction

`InternedRecordCoherence` closes the global cache-to-payload obligation for
the executable constructors in `InternedConstructorTemplates`. It derives
the invariant from finite construction traces that start with both caches
and both payload tables empty.

## Derived invariant

`Coherent` states that each edge payload has its canonical cache entry. Its
ordered child references equal the children in the complete edge key. Each
node payload has the canonical entry for its constructor key. Ordinary node
keys contain the actual edge identities. Union keys contain the actual member
references. Their stored depth and free-reference fields equal the source
computations on those children. Mu keys contain the references of the two
stored probes.

`Covered` states the converse: each identity entry has a payload. An explicit
list permits pending Mu records during identification. `reserve_correct`
adds one pending key. `complete_correct` removes it after body construction.
This list permits duplicate keys; the theorem does not assume distinct pending
keys or certify that forcing a pending Haskell record terminates.

`compile_safe` derives the required callback field equations by recursion on
the actual argument, capture, node, edge-list, and union templates. It uses
the source smart constructors, including edge sorting, deduplication, empty
cleanup, union flattening, and the ordinary-union path. It does not take
whole-template coherence as a premise.

`constructed_correct` derives `Coherent` and `Covered []` from the actual
empty-state trace. Its steps execute generated ordinary templates or the
two-probe Mu constructor and cleanup. The Mu body remains the ordinary
template fragment. Its pending-key noninterference comes from the existing
`compile_preserves_mu` and `finishMu_miss` theorems.

## Canonical readback and finite inventory

`node_readback` and `edge_readback` connect every completed identity-table
entry to its exact payload and field equations. `node_identity_unique`
proves that equal identities of stored node records imply equality of their
complete payloads. This includes their stored metadata and children.

`nodeInventory` reads the issued keys at the finite range below the actual
node counter, then reads their payloads. `node_inventory_exact` proves that
it contains exactly the completed node records. `node_inventory_bound`
bounds its length by the counter. `mu_inventory_member` includes the raw Mu
record even when the public constructor removes that redundant binder.

This inventory describes one completed finite construction trace. It is not
an a priori bound on all records that later substitutions or exposure can
allocate. The existing replay theorems still provide that stronger fixed
result only for a fixed generated request and table growth.

## Source boundary

The source correspondence uses `Interned/Type.hs` identification and smart
construction. `identifyNode` computes the ordinary and union metadata.
`UninternedMu` equality uses both probes. `createMuDontCleanup` constructs
those probes before cache insertion. `Cache.intern` installs its candidate
without forcing the strict Mu body during the atomic table update.

This module certifies records inserted by the generated operations. An
arbitrary captured value or supplied recursive reference can still contain
invented identities or metadata. A trace can use such an input, and the
new enclosing records still retain its actual fields. The theorem does not
claim that this certifies the input's descendants. A complete source graph
adapter must obtain captured values from prior source construction or require
their recursive representation invariant.

Generated nested Mu callbacks remain separate. Their body computations can
request Mu keys. The source `internedMuBody` field is strict. A request for a
currently incomplete Mu can therefore force its own unfinished record.
The ordinary-template disjoint-key proof does not cover that case. A full
nested proof must derive either a different key or an already completed
record from template structure and fresh outer-reference provenance. Mere
`Covered` membership or HOAS totality does not establish this condition.

Validation on 2026-10-12: `lake build MicroCFTA.InternedRecordCoherence`
passes with 107 jobs. All 31 theorem axiom checks use only `propext` and
`Quot.sound`. No new axioms, incomplete proofs, Haskell edits, or Cabal runs
were added.
