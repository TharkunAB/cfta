# Encoded enumeration-slot writes

Updated: 2026-10-24. Baseline: `597dc875e576d348073d03c49e3aa8ab523b33c3`.
Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.
Proof: `5574e476b4fefd2a6716813ea483bab374c41367`.

`SourcePruningEnumerationWrites` proves two actual modeled slot operations.
Both start from a Coherent native heap, an Available closed complete Value and
incoming PendingRealized. Both derive the written handle through the actual
computed codec. The native heap stays the same. EnumGuard and NativeGuard
remain independent. Full Values and Symbol refinements remain intact.

`allocate_available_realized` also assumes counter/value-list alignment.
It derives the actual allocation success, returned raw UVar, exact fresh-slot
readback and PendingRealized of the complete allocated state. This includes
the incremented counter and inherited ancestry. Alignment binds the returned
counter to the appended slot. The invariant alone does not imply alignment.

`write_available_realized` also assumes an in-range raw slot. It derives the
actual setValue success, exact whole-state record update, written-slot readback
and PendingRealized of that state. The suspended list is arbitrary. Its order
and duplicates remain. The slot need not be a union-find representative.
The in-range premise excludes a silent out-of-range List.set and the native
setter's missing-old-slot lookup boundary.

Both proofs cover every pending slot, including unused and nonrepresentative
slots. An actual post-write payload is either an old payload or the newly
encoded payload. The old case recovers a genuine old list index. The new case
uses exact constructor equalities and the derived native readback. No selected
handle, successful decoder, desired final invariant or replacement heap is a
premise. No helper, definition, type, instance or induction is added.

The module has 69 lines and two theorems. It is below the estimated 70–115-line
target and within the hard 135-line limit. No padding is added. Strict Lean
4.34.1 passes on the first attempt with all linters and warnings as errors.
Its raw log is empty. The installed build passes 563 jobs. Aggregate
Audit passes 3682 jobs and 76103 theorem dependency checks. Its only
warning is the older unused-input warning in InternedFreshOrdinaryClosedCompletion.
Both full public signatures and both actual axiom reports were read.
Each theorem reports only propext and Quot.sound. Independent declaration,
body and public reviews clear the component.

The original declaration owner retains 42 payloads and three STRING contracts:
seven context lines and 24 public header lines. Both statements and the full
scoped inventory remain unchanged. There is one successful strict input and
no failed compiler attempt for this component.

These are exact operations in the existing modeled value/ancestry state.
Native allocation and replacement also maintain expandable and waiting indexes.
Their correspondence is not proved here. Theorems do not certify native state
equality, Int/NodeId extraction or acceptance of Empty by the full driver.
They do not derive StorageValid of arbitrary suspended lists.

Next compose actual native narrowing with these writes. Retain the derived
heap, all old slot certificates, Empty rejection and the unchanged-ID branch.
General intersection/assimilation still needs a concrete native operation and
its exact handle/heap correspondence. Open-hole bounds, ordered observation
batches, lazy native emptiness calls, typing, outer narrow, memo2 and typedTypes
remain separate. The frozen producer plan retains the original proposals and
their source-only status; these two results complete its allocation/write part.

H6 remains the strongest combined theorem. Covered closed construction and
valid original guard/cache history derive sufficient mathematical width/fuel
for any finite number of modeled node-call rounds. Empty inherited payload
gives exact finite-tree language equivalence. withoutRedundantEdges and
convergence remain outside that theorem. These writes add no language theorem.

Native extraction, index-cache and graph realization, global helper canonicality,
canonical mutation histories, selected-current protection, cached scheduling,
semantic pruning, phase 4, resources, practical width, runtime/solver and
convergence remain open. H23 stays queued. The full goal remains active and
incomplete. Older proofs, counterexamples, repairs, drafts and the optimized
interned core remain preserved.

No Haskell source changes occur. FINDINGS keeps the external repair index first.
All six recorded repairs are on main. No additional patch remains for those
six defects. Evidence is in restart-evidence/20261024-pruning-enumeration-writes.
It retains the frozen owner, all attempts, reviews, exact baseline, capped
resource receipts, previous publication receipts and the frozen producer plan.
