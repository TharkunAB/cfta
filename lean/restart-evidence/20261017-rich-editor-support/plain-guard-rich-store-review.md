# Rich stores through actual constructor and head returns

Reviewed on 2026-10-17 02:47 CEST.

`SourceCurrentConstrainedCapRichStoreEffects` has three public producers. Each returns the exact `advanceHeap` state of the literal constructor result or supplied actual head result. It retains `SharedSupport.Stored` before returning existing physical readiness, effects, and result availability or residency.

The store has three independent causal components. The native component contains the Mu representation invariant and source-universal conditional native laws. The Merge component belongs to each actual earlier Merge entry. The target slot component refers to the same captured class record, original forest, and slot path. Constructor and head advancement leave the Merge table and slots unchanged. The helpers retain these components without replacing their captured parameters.

`node` derives Mu retention from `MuStored.makeNode`. It obtains readiness, physical effects, and availability from the actual `node_physical` helper. `edge` uses `MuStored.makeEdge` and actual `edge_physical`. It retains the full raw guard and exact ordered child list. It does not require a hereditary guard or reject a nullary edge. Field availability is a successful normalized readback condition. It is not constructor acceptance or a plain-guard assertion.

`head` needs a closed available input with an initial finite cap. `CapExposure.head` derives the causal Mu store at the actual returned heap and the same-depth output cap. The existing actual head support theorem derives all-path `Preserves` at that same result. The physical helper supplies readiness and availability. The rich store advances only after the actual output Mu store has been derived. No whole-heap guard condition, leaf callback, desired output annotation, or future completed body appears in the public inputs.

## Validation

The production source is frozen at `377d01a06e52e12f571da60ae9e5f122130331cb494a76257197cdd7559c06f0`. Direct strict checking passed on its first attempt. The log contains zero bytes. Root canonical `forest-store-build.log` passed with 1388 jobs. Its only warning is the existing `InternedFreshOrdinaryClosedCompletion.lean:24` dependency warning.

The imported public probe has three axiom reports and three full signatures. The two imported integration kernels passed on their first attempt. Printing includes explicit arguments, proofs, universes, deep terms, and a 10000000 step limit. Both logs have no errors, warnings, `sorryAx`, or truncation marker.

`raw_guard_then_node` performs actual edge work followed by actual node work at the first returned heap. It derives a cap of depth one from hereditary children without assuming that the raw guard is plain. It verifies the raw guard readback, rich stores, current readiness, and exact unchanged slots and Merge memo.

`own_head_then_node` constructs its own finite `Head` from initial ready, closed, available input facts. It then rebuilds the actual exposed rows at the returned heap. It derives the final rich stores and readiness, exposed and rebuilt caps, all-path input-to-head preservation, and exact captured slot and memo retention. No completed head or intermediate-store premise is supplied.

## Scope

The constructors execute their literal finite work. Head preservation follows an actual head graph; the integration kernel constructs that graph with the existing finite head theorem. This component does not prove edit-wide store retention, native or Merge resource bounds, general selected-class closure, or general recursive reduction termination. Those claims require separate producers. No Haskell source changed.
