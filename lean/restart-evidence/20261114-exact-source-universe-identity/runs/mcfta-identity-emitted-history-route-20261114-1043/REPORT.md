# Identity eager outputs: exact history route

Status: bounded source review and target headers only. All four header files are UNCOMPILED. They contain no proofs. This task ran no Lean command, evaluator, runtime probe, Git command, or board command. It made no live source or Haskell change.

## Result

The existing configured eager resource theorem already retains `PendingReferences` and an existential dependency level/frontier at every emitted output of its certified outcome. The missing bridge is an actual identity-narrowing resource producer. Metadata erasure does not bridge different narrowing callbacks.

A second distinction matters. Existing whole CPS closure produces one stable outcome for all sufficiently large work fuels. It does not establish the same invariant for outputs emitted at arbitrary smaller work fuels. The two target scopes are separate files.

## Existing endpoint closure

1. `SourcePruningEnumerationRecursive.Packet` in RecursivePacket20–35 contains `pending` and `ordered`. These are exactly `EnumerationReferences.PendingReferences before.core` and `∃ level frontier, EnumerationOrder.Stratified before.core level frontier`.
2. `SourcePruningEnumerationSharedRecursive.OutputResources` in SharedHookCertificates110–119 contains an actual output packet, full native Post, output queries, and original resource bounds. It retains that output's own cache and caller. SharedPreparedHookCertificates51–56 aliases this contract for the prepared worker.
3. `SourcePruningEnumerationSharedPreparedRecursive.OutcomeResources` in SharedPreparedOutcomeResources32–48 supplies OutputResources for every output in both `.complete` and `.stopped`. A stopped result can retain earlier outputs. The desired output invariant follows by projecting `packet.pending` and `packet.ordered`; it does not require the final endpoint to emit another result.
4. `SharedEagerReservation.runEager_finite_complete_resources`3712–3732 proves a stable configured `runEager holeKey fits admits ...` outcome for all `bound + extra`. Its private `EagerResumeComplete`880–906 has the same configured narrowing choice. The appearances of `resumeWithNarrow` in proof bodies unfold the configured wrapper. They do not make the theorem polymorphic in `narrow`.
5. `CurrentProgramEagerResources.accepted`46–103 starts from the actual accepted Current source and returns this configured resource closure. `CurrentProgramEagerOutputs.accepted` also projects an output packet and explicit levels. This is existing configured coverage, not identity-worker coverage.

## Same initializer: no missing initial witness

Call `SourceSynthesisCurrentProgramSlotsInitialization.accepted` once, at width `enumBits lib query signed depth + 2`, with Cache.emptyState and its validity proof. Keep its fields/cache/value/heap/build receipt, original guard receipt, Context, Facts, Available, closedness, original/value roles, handle, and ProgramSlots.

Use `Recursive.initial_packet_carriers` in InitialCarriers27–48 with that exact Context, same decoded value and heap, and canonical `Metadata Unit := ⟨[], [], [], ()⟩`. It derives the initial Packet, canonical core, root storage, zero suspended bound, waiting counts, flags, graph carrier, and reference carriers. It also produces the handle. The accepted source proof identifies this handle with the original one using their common encoding. Do not allocate a second heap or provide another caller.

The current proof in CurrentProgramEagerResources104–138 already performs these operations. It derives Fits from reflexive numeric bounds plus `InternedValueMassHeap.initial`, Heap from `SourceCurrentConjunctionGuardUniverse.initial`, and the reservation from `CurrentProgramEagerEnumerationWidth.eager_reserved_of_build`. These are original-source producers. They need no Key/fits/admits argument. Only the subsequent whole-worker theorem currently uses configured narrowing.

`CURRENT-TARGET-HEADER-UNCOMPILED.lean.txt` preserves the entire initializer conclusion prefix byte for byte. It fixes identity narrowing, empty templates, no stop, no preference, actual nodeEdges, and canonical Unit metadata. It asks for the same whole resource result and explicitly projects the two desired output invariants. It has no future Context, output packet, trace, callback law, or semantic provider premise. The old configured theorem remains separate.

## First concrete missing producer

`FIRST-PREFIX-TARGET-HEADER-UNCOMPILED.lean.txt` is an identity specialization of `SharedRecursive.prefix_complete_resources`162–181. Its premises are only the same original packet/resource inputs. It fixes the callback itself; it does not ask the caller for a proof that an arbitrary callback behaves correctly.

The existing `SelectedStep.runPrefix_identity_selected_complete` in IdentityCompletion31–92 already derives actual reads, checks, ready/cache fields, IncomingAvoid, and PendingReferences transport from the original selection, native readiness, Safe, realized handles, roots, counts, and flags. It handles repeated true, Empty rejection, and nonempty identity preparation. Its actual nonempty action is `pure ()`, at the unchanged native heap, with the literal advanced caller. It does not return an ordered Packet, whole Context/Post, or a resource certificate.

The remaining local work is concrete:

- derive its selection and readiness premises from the original packet and actual Restart.decision;
- retain dependency order through the actual read/check; PrefixHistory.complete11–58 handles the false-check frame/pending replacement branch; true clear instead needs the actual representative frame and pending-to-pending write order law, because that theorem assumes a false observation;
- build Packet at the actual parked cache and at the literal identity advanced caller;
- derive actual Post/resource fields for the unchanged native heap and operations;
- use empty-template callback operations to retain the packet. No future callback law is an input.

This header is a target, not a claimed producer. No proof credit is assigned to these transports yet.

## Actual fragment-history producer chain

The identity worker keeps the same eager child operation. `runEagerWithNarrow` in SharedPreparedRecursiveChildPolicy147–158 is `runWithNarrow` with the existing `eagerChild`. Its selected nonempty branch57–75 runs the existing shared prepared child policy and recurses with the same fixed identity callback. Native child conjunctions, ordered scans, sibling caches, and emitted outputs are unchanged operations.

`SharedNativeBranchCompletion.head_complete_resources_prepared` in SharedNativePreparedResources36–73 derives an actual CapturedEdge receipt, Post, Admitted, Pending transport, FragmentHistory, and resource advancement. Its InputsPending premise is obtained from the current packet's PendingReferences and the actual stored pending bucket. Ready, realized/cache fields, roots/counts/flags, available closed parent, edge membership, and original budgets must come from the actual reached prefix and existing CPS resource proof. They are not supplied as future invariants.

Its `FragmentHistory` is the SHARED receipt contract in SharedHookCertificates43–49. For each completed fragment it derives counter growth, PendingFragment, and transport from the old stratification to a new level at frontier + 1. `SharedPreparedRecursive.receipt_packet` in SharedPreparedHookCertificates32–48 combines that history with actual Admitted, Pending, and Context to build the callback restart Packet. `Recursive.captured_post` and callback/frame laws retain the captured cache and its invariants through actual native endpoints and callback reads.

The existing whole CPS resource proof already closes these operations for configured narrowing. `INTERNAL-RESOURCE-TARGET-HEADER-UNCOMPILED.lean.txt` is the exact fixed-identity endpoint contract needed to reuse that architecture. Its initial Packet/Fits/Heap/reservation inputs are all derived by the source initializer above. It has no future provider premise. Proving it still requires an actual identity recursion/child/tuple/rows composition; changing the final wrapper name is insufficient. Start with the prefix producer before expanding that proof.

## Metadata and fuel scope

`IdentityWorkerMetadataErasure.runEager_identity_metadata_erasure`382–396 compares two executions that BOTH already use identity narrowing, empty templates, no stop, and no preference. `CurrentInitialIdentityMetadataErasure.accepted_initial_identity_worker_erasure` gives the same accepted initializer and corresponding outputs with equal cache/caller/queries. Once canonical Unit identity output history is proved, apply the GENERIC worker erasure theorem at those already chosen initializer witnesses to transport history to arbitrary metadata. Do not call a second existential accepted-source theorem and silently identify its witnesses. Erasure itself supplies no PendingReferences or Stratified proof and does not replace the resource bridge.

`CURRENT-TARGET` covers all outputs of the stable outcome at `bound + extra`. `ALL-FUEL-TARGET-CLAUSE-UNCOMPILED.lean.txt` is the stronger every-workFuel conclusion at the SAME initializer. It includes outputs retained by stopped results. Existing stable CPS completion does not imply this stronger clause. It needs a separate fuel-parametric actual safety induction or an established low-fuel output inclusion result. Neither was found or proved in this bounded review. Do not silently claim all-fuel coverage from the stable result.

## Boundaries and receipts

This route would establish reachable output-history coverage. It would exclude stored dependency cycles touching an enumerated record through the newly checked dependency lemmas. It would still not produce one finite shared assignment for all original roots. The pure proper-path cycle no-assignment law is already checked. PendingReferences and Stratified do not exclude a cycle whose records are all pending. Showing that actual emitted outputs have no such residual obstruction is still separate from the checked cycle law. Common assignment construction, original-root witness recovery, complete original-resource coverage, both workers, and Haskell correspondence retain their prior proof boundaries.

No Haskell defect or fix was found. No FINDINGS change is needed for this header review. Root reported six dependency lemmas passed a private check; this task did not rerun or inspect that compiler evidence.

SOURCE-PINS records 26 current file identities. It is not a whole-source semantic review certificate. SOURCE-SCOPE records named cuts/locators and the earlier truncated output incident. Unrecovered text is not claimed as read. Historical acquired/reserved whole slots, unions, permanent FAILs, and indirect/unrecorded UNKNOWNs are not reset or certified by this task.
