# Computed narrowing and enumeration branch effects

Updated: 2026-10-24.
Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.
Proof: `7ef31cf002475708fd6b5b7b8427b6ea34f3e845`.

## Exact result

SourcePruningEnumerationNarrowing composes one actual native-model narrowAt
computation with the enumeration branch effects. Its inputs are Ready for the
native heap, realization of all pending slots, Total root paths, an actual
pending getValue success, and a full Frame to the branch entry state.
The source alphabet includes full formula labels. The enumeration guard and
native guard types remain independent. The key type remains generic.

The actual stored pending slot derives the complete old Value, its successful
lookup, availability, closedness and encoding at the captured old handle.
One narrowAt_complete application derives the actual result and native heap.
The theorem retains its selected fuel, larger-fuel stability, Keeps, complete
result availability and closedness. Final coherence derives the new encoding
and complete readback. Keeps retains the complete old lookup in the same final
heap. Full frames and Keeps retain realization of every pending slot at entry.
A surviving result also derives that the old Value was nonempty.

The output gives the three branch implications in source order. Empty has no
successful reject continuation. Equal surviving handles imply equality of the
complete old and result Values. The literal pure continuation retains entry.
The native heap remains the actual narrowing output in this branch.

Changed surviving handles derive a finite actual representative reread. Its
root, original root path and size, actual compressed state, complete frames,
old pending slot, ordered suspended list and list bound remain. The actual
write consumes that compressed state. It writes the computed result handle
at the returned raw root with the same suspended list. The output retains the
exact final record update, new slot readback and realization of every pending
slot. It also retains Success for the literal representative/write bind through
that actual intermediate state. There is no Frame claim across the value write.

No old Value, new handle, final heap, second representative success or desired
output equation is supplied. No new action, carrier, predicate, helper or global
instance is added. One local Monad List instance uses the existing singleton
and flatMap convention for the literal pure and bind expressions.

## Validation and retained work

Strict checking passes on the first attempt with an empty log.
The installed build passes 566 jobs. Audit passes 3685 jobs and
76119 dependency checks. The existing warning remains in
InternedFreshOrdinaryClosedCompletion. No new-source warning occurs.
The complete actual public signature and axiom report were read.
The theorem uses only propext, Classical.choice and Quot.sound.
The first public output succeeds but abbreviates the final branch. The second
output retains all 101 lines after two display-only pretty-printer settings.
Both actual inputs and outputs remain. The production proof has no options.
The 104-line module adds one theorem. The frozen owner retains 83 payloads,
nine literal fragments, seven local have types and six obtain groups.
All frozen declaration fragments, scoped types, source snapshots, API cuts,
independent reviews, raw compiler results and capped resource receipts remain.
The full baseline contains 129193 tracked files. Earlier sealed evidence
remains unchanged. The preceding checkpoint's post-seal receipts remain.

## Next proof and boundaries

Connect the outer source narrow wrapper to its Mu and type-position bypasses.
Use the original selected raw UVar in type-position and holeKey tests. The
representative returned by the second read determines only the write address.
The generic key does not establish the typing meaning of fits or admits.
The retained source-only outer-wrapper plan includes fifteen complete source
snapshots and exact cuts. Its proposed wrapper is not yet implemented.

This component does not yet connect the computed native result to the pure
Nat narrowing callback and graph classification in EnumerationUntil. It does
not include the subsequent oracle or continuation. Common numeric fuel bounds,
native NodeId extraction, waiting and expandable index caches, intersection
and assimilation, open-hole bounds, ordered reads, lazy emptiness, memo2 and
typedTypes remain open. Global helper canonicality, mutation histories,
selected-current protection, cached scheduling, semantic pruning, phase 4,
resources, practical width, runtime/solver correspondence and convergence
remain open. H23 and the older constructor/equality targets remain queued.

H6 constructed_node_calls remains the strongest combined theorem. Its covered
closed construction, valid initial cache, original guard allocations, finite
rounds and empty inherited-payload conditions remain.

No Haskell source changes. FINDINGS keeps its external repair index first.
All six recorded Haskell fixes are on imported main. Earlier proofs,
counterexamples, repairs, marked drafts and the optimized interned core remain.
The full goal stays ACTIVE and incomplete. This note precedes evidence creation
and the authorized push.
