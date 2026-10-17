# Initial selected projection integration

Reviewed 2026-10-17 10:15 CEST. The final standalone source is `initial-projection-kernels.lean`. Its exact snapshot is `initial-projection-kernels-2.source.lean`. The successful strict log is `initial-projection-kernels-2.log`. All four public theorem pairs have complete explicit, proof, universe, deep-term, and full-name settings. The only axioms are propext, Classical.choice, and Quot.sound. The first failed source and full log remain unchanged.

Each kernel starts from its own literal source construction and derives SemanticReady, the causal cost heap, availability, and initial Fits from the constructed store. It calls `SourceCurrentProjectionNumeric.complete`. It supplies no completed projection, future heap, numeric result bound, or readiness certificate. A separately computed finite worker run identifies the returned value and full heap by graph uniqueness. This comparison does not become an input premise of the kernel.

`recursive_initial` uses an explicit union that contains a productive raw Mu and an ordinary constant. The selected node path is `[0,0]`. The equivalent forest path is `[0,0,0]`; its first index selects the original root. Independent concrete reductions prove that this projection strictly increases both node and edge counters. The kernel then derives the exact graph, computed worker/read execution, final Fits, result mass bound, and every larger pair of proof fuels from initial facts. The computed majorants remain symbolic.

`selected_beside_open` runs the actual complete endpoint on the forest `[input,reference.depth]`. It proves ForestClosed for the selected proper path and proves that the complete forest is not ClosedValues. It returns the same concrete projection value and full heap with computed Fits and a closed available result. This kernel executes projection through the open-sibling forest; it is not only a domain witness.

`signed_missing` invokes the initial endpoint separately at negative index -1 and absent positive index 99. Both return Empty and the exact original full heap. The proof supplies a vacuous selected domain, not global forest closedness.

`root_duplicates_warm` invokes root union on two occurrences of the same recursive union operand. It retains the actual graph and proves that the result language equals the single operand language. The second call starts at the full first returned heap. Its semantic heap, cost heap, operand availability, and initial Fits come only from the first constructed result. It returns the identical value and full heap at the newly computed initial bounds. No future counter or store premise is supplied.

Allocation inequalities are proved only for the two-step recursive node path and its equivalent singleton-root forest execution from the original source heap. The open-sibling kernel identifies that same returned heap. The signed missing cases preserve the heap. The duplicate root kernel proves exact warm full-state identity; it does not assert a separate strict allocation inequality for the root-union branch. These are selected projection checks. They do not execute a complete Operand, Merge, Target, or constrained reduction and do not establish host-runtime correspondence.

Frozen production hashes reviewed here:

- `SourceCurrentProjectionNumeric`: `966bb576ac32c9345d4e8723ffac08ee2c0405abd018610b750cf290ec95f531`
- `SourceCurrentProjectionInitialResources`: `aba0dc2fea3a245e5d53b4708cfd67a33702ed900b286a2dd8d69e48aab61f49`
- `SourceCurrentProjectionNumericControl`: `6683ba7b88f971c199d6455598ade439e23bb1547b55295e72878df716bbe725`
- `SourceCurrentProjectionNumericReplay`: `53600902e69c0bfb9d924e2adef0d2f378c0d08fc39584e348c6ce476583411d`
