# Edit and class initial capacity validation

Date: 2026-10-16 21:46 CEST.

Production sources are frozen:

- EditInitialCapacity: bff4c68beacc761d7bb09b9a7da37b3f13a426e21e01dfe1b3df55c44381abf4.
- ClassInitialCapacity: 28bcf356c321bc60d6439774e181be525c94eb5cbbde65c867fdce50fe149e0e.

Pinned Lean is /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean. Direct checks use the canonical lean/.lake/build/lib/lean import path, with unusedSectionVars and unusedVariables enabled. Probe sources also print explicit, deep, full-name signatures without truncation. Root owns all canonical Lake processes.

Final results:

- edit-initial-direct-3.log: terminal 0, no diagnostics.
- class-initial-direct-2.log: terminal 0, no diagnostics.
- edit-initial-capacity-build-1.log: root canonical terminal 0, 1376 jobs.
- class-initial-capacity-build-1.log: root canonical terminal 0, 1388 jobs.
- edit-class-initial-public-2.log: terminal 0; 5 full signature and 5 axiom reports.
- edit-class-initial-kernels-2.log: terminal 0; 4 full signature and 4 axiom reports.

Canonical logs replay only the historical InternedFreshOrdinaryClosedCompletion inputs warning. Direct final and probe logs contain no error, warning, or sorryAx. Axiom reports contain only propext, Classical.choice, and Quot.sound.

The integration kernels derive existing node and list range plans, derive compiled class ranges, and construct the actual class plus literal stable worker from initial resources. They do not take a completed graph or numeric capacity plan as an initial premise.

Preserved attempts:

- Edit direct 1: one missing qualified edge_physical name.
- Edit direct 2: omega required an explicit definitional view of counters after advanceHeap.
- Class direct 1: an isolated temporary import root shadowed the canonical MicroCFTA package. No production proof failed in that attempt.
- Public and integration probe attempt 1: pp.maxDepth is not a supported option. Attempt 2 uses pp.deepTerms and pp.proofs. Source snapshots and raw logs remain.

No Haskell, older proof, Audit, restart authority, or Git change was made by this component. Read edit-class-initial-review.md for the exact capacity and resource scope.
