# Stored rebinding boundary

The checked source is a closed raw outer Mu.
Its body is `node f [outerSelf, rawMu (node g [outerSelf])]`.
The outer local occurs below a constructor, so `usesLocal` is true.
The inner Mu ignores its own local, so its `usesLocal` is false.
The original ordinary probe retains that raw inner Mu.
The repaired stored compiler encodes every open stored Mu as a smart binder.
Rebinding the outer stored body therefore removes the inner raw wrapper.
The actual rebuilt result is physically unequal to the actual ordinary probe.

`witness` constructs the source execution, source Facts, and availability from empty.
It checks the selected outer table record, closedness, both local-use decisions, and successful actual rebinding.
It supplies no future successful execution, desired row origin, Cap, or prepared-body premise.
The witness uses generic Nat symbols and Bool guards.
It refutes an overstrong generic physical equality. It is not a Haskell defect or a nontermination result.

The additional integration checks the same fixture.
Both root rows retain symbol 0, literal guard false, arity 2, and the first child in order.
The unequal ordinary-probe child returns the exact rebuilt child after one actual repaired Mu unfold.
That unfold retains the complete heap.
This shows why an epsilon relation can retain the required row correspondence.

Selected evidence is direct-3, canonical-2, public-3, and kernels-3.
The final strict source log is empty. Canonical builds 260 jobs.
Public printing checks the full theorem statement, checked private proof reference, and allowed axioms.
The construction proof is factored privately to avoid expanding its large reduction proof in public output.
Public attempt 1 has a pretty-printer failure despite exit 0 and is not selected.
Public attempt 2 stops with exit -15 and is not selected.
Failed direct attempt 1 and row integration attempt 1 remain preserved.
All imported selected sources explicitly set the eight required options.
Each selected run reads back memory.max = memory.high = 4294967296 and memory.swap.max = 0.

# Proposed next producer, not proved here

The exact selected winner already has the current complete probes by `SourceCurrentNativeRequestProbes.request_probes`.
`SourceCurrentNativeMuPublication.History.from_empty` identifies its actual earlier writer and three callback histories.
`InternedFreshOrdinaryPlanEquivalence` compares equal resolved inputs, not nominally different callback outputs.
`InternedFreshOrdinaryLiveInputReplay` also requires agreement of live inputs.
`InternedGuardedProbeHeap.Correct` gives least-language equality, not literal row occurrence transport.
It does not preserve nonproductive row witnesses or expose their exact guards and ordered children.

A useful proposed endpoint starts with Ready at the current heap, actual History from empty, the selected Mu record, `usesLocal = true`, and an available arbitrary replacement.
It constructs the stored-body execution with self replaced by that replacement.
It then constructs the ordinary-probe execution with its selected ordinary name replaced by the same replacement, starting at the first returned heap.
The proposed result is equality of the two returned values in the common final coherent heap, together with the actual calls and retained histories.
Do not require equality of both full outcomes from the same starting heap: row execution order can change allocation order.
No successful alternate call or desired stored relation is an input to this proposed producer.

The two reconstructions must normalize both operands. The checked witness rules out comparison with the unreconstructed ordinary probe.
Actual writer freshness supplies disjointness from every live fixed capture; it must be derived for both ordinary and reserved assignments.
Nested retained Mu branches must use the earlier selected writer, not a losing candidate.
The missing proof is simultaneous source reconstruction fusion and causal first-writer retention.
Any heap-dependent proof also needs actual growth to its common view. `History.retain` alone supplies only NoNewMu.
This proposed equality remains unverified. If it fails, the residual target is epsilon row simulation with exact guard, symbol, arity, and ordered related children.
