# New refolding and reduction-birth order: read-only review

Date: 2026-10-16 04:47 CEST.
Source baseline: b09f4ebb, including main d44b2a0f.
No production source or proof module was edited for this review.

## Source sequence

`Interned/Operations.hs:211` defines `refoldEdges`. An empty recursive-unfolding map returns `(n, id)`. Otherwise one memoized `mapNodes` step is shared by all iterations. A changed root advances to `x'` and composes `rebuild . edgeOf`; a stable root returns the current root and accumulated edge map. Rebuild changes only the ordered children through that same step. The source explicitly limits the map to input edges.

`Gen/Synthesis.hs:625` defines `orderedSpace`. It obtains original births, the last input space, and the space count. It refolds that last space and transports original birth indices of its reachable edges to the keys of their mapped edges. `IntMap.fromListWith min` retains the earliest of colliding mapped-edge births. `IntMap.unionWith min` combines those entries with all original births. Unknown edges get the space count. The weight is the negative conversion to Double.

`births` scans the spaces in order. It rejects an empty history. It visits each immutable node identity once across all spaces, records each outgoing edge with first-insert-wins, and then visits its ordered children. A node seen in an earlier round needs no second scan only if an identity always names the same complete record and outgoing edges.

`Enumeration.hs:669` orders edges by stable descending weights after canonical order. The weights steer order and do not select edge membership. The canonical-order and generated-node fallback paths remain relevant.

## Adapter obligations

1. Finite total histories, source node exposure, and traversal termination. `reduceWithOrder` supplies a nonempty bounded reduction history, while exported `orderedSpace` accepts arbitrary finite-list inputs and throws on the empty list.
2. One actual shared refold step, stabilization of its unbounded loop, and the accumulated input-edge map. The source test covers a simple refolded child. A proof must establish that the source callback, Mu probes, recursive placeholders, and rebuilt edges realize the finite model. A bare language-equivalence assumption does not establish physical edge correspondence.
3. Interned node and edge identities must be faithful and immutable. Node and edge keys are signed machine integers in Haskell. Lean natural-number identities alone do not establish machine bounds or process-level identity behavior.
4. The first-insert and minimum-collision laws of the actual IntMap operations. Refold transport can merge multiple original edges, so last-wins aggregation would be wrong here.
5. Exact stable sorting and Double comparison. The normal reduction history has at most 31 spaces, so those birth weights have exact finite Double representations. Arbitrary enormous public histories require a separate numeric adapter. Enumeration fairness and exact global output order need the existing enumerator correspondence as well as these local weights.
6. Injective renaming of process identities must preserve lookup and graph correspondence. This is needed before a theorem about abstract tables can establish independence from process allocation history.

No concrete source defect was found in this review. These are proof boundaries, not asserted bugs. No runtime or whole-source ordering theorem follows from the proposed component alone.

## Implemented bounded proof component

The parent approved `SourceCurrentReductionBirthOrder.lean`. The module is now implemented and frozen; its separate validation note records the exact scope and checks. Model the finite first-insert birth table, the final-edge transport entries, min aggregation, min union, and unknown-edge fallback. Prove that a known key receives exactly its earliest original or refold-preimage birth; prove invariance under an injective key renaming; prove unknown keys use the count while bounded known births precede them. Keep traversal, source refold/mapNodes execution and language preservation, actual machine maps, numeric conversion, and exact enumerator order as explicit adapters.

This component would not modify or replace the recursive checked Mu proof and would not assert completed end-to-end order correspondence.
