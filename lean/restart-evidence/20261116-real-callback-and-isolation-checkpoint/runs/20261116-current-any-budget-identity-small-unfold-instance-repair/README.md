# Small unfold and instance repair

Status: UNCOMPILED. No full worker proof is included.

The prior small component check failed at two locations. The generic alphabet `rfl` reached the 2M WHNF limit. The actual branch header could not synthesize `Pure (EnumerateM Symbol Constraint)`. The original success and Empty propositions passed the separate type-only check at 500k. Their elaboration is not the source of the earlier 8M proof failure.

This packet changes only the alphabet proof and the local instance setup. The alphabet proof explicitly unfolds `SharedPreparedReservation.preparedSeed` before `rfl`. The preamble enables the existing `SourcePruningEnumerationAction.actionMonadList` local instance. The actual branch header, runtime arguments, branch proof, and component probes are unchanged.

Append `APPEND.lean.txt` to the current owner. Append `COMPONENT-PROBES.lean.txt`. Use a unique log name for this job. Do not append a full worker consumer or any already published component. The checker limit remains 2M.

Run `PreparedSeedAlphabetGate.lean` as a separate normal-import Lean file. Append `NORMAL-GATE-PROBES.lean.txt`. This gate imports only the public prepared reservation module. It deliberately uses the original plain `rfl` proof, without owner declarations or local opacity attributes. Its 500k limit gives a small independent comparison with the owner failure. This separate file does not belong in the owner append job.

The original alphabet and branch headers remain byte-exact. The original public worker declaration and all retained resource headers also remain byte-exact. The JSON compatibility file records their hashes. The original failed packet and logs are unchanged.

No compiler, live source, Git, board, Haskell, or temporary-directory action was performed. The full any-budget worker theorem and the full compatible finite accepted-completion objective remain open.
