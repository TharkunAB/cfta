# Exact successful-preparation resource transport

Status: UNCOMPILED proof candidate. Root owns strict Lean validation and publication.

Add only `lean/MicroCFTA/SourcePruningEnumerationSelectedPreparationObservedResources.lean`.
No live source has been changed. The patch adds one standalone proof module.

The theorem is `MicroCFTA.SourcePruningEnumerationSelectedPreparation.successful_resources_current`.
Its first parameters are exactly those of the checked `complete_resources_current` producer.
It then takes one actual observation at the supplied common entry/native fuel.
The observation preserves the full row, returned core, normalized result, and native heap.
There is no eventual-observation, future-resource, or callback-provider premise.
The existing initial Packet, Ready, stored bucket, Fits, IncomingAvoid, and Heap premises remain explicit.
Fits is the original allocation-resource premise. No replacement fits or admits relation is introduced.

The conclusion retains every resource and semantic field of `complete_resources_current`.
It gives the actual caller advanced by the supplied returned heap.
It uses exactly `EnumerationExpandableIndex.frame entered before` as the returned cache.
It preserves Post, Packet, RenderStable, Ready, stored bucket, counter, values, cache and waiting indexes,
Available, closed free variables, meaning equality, assignment satisfaction transport, normalized Fits,
value mass, Heap, IncomingAvoid, and exact suspended mass.
It also identifies the observed target, handle, and suspended bucket with the original selected slot.
The stable observation tail starts at the actual supplied small bound and retains its exact fields.

Proof route:
1. Obtain the checked current producer's own eventual bound and full resources from the same initial inputs.
2. Replay the actual successful observation to `fuel + bound`.
3. Compare it with the producer observation at `bound + fuel`.
4. Project exact equality of the entire raw row/core and the entire done result/heap.
5. Use the producer's frame receipt to identify the whole returned cache with the actual framed core.
6. Substitute the equal result fields and return all producer resources for the original observation.

The dependency `SourcePruningEnumerationSelectedPreparationReplay` is the unchanged repaired candidate
that Root reported strict PASS with two standard-axiom reports at 15:28 CET.
Its canonical source SHA is f5375863081ea8a1b877f6c093378c042cdf5ec05f6c910a5508be4b6d45e31d.
`CHECKED-REPLAY-DEPENDENCY.lean.txt` records that exact source without print commands.
This text file is a review artifact. It is not a namespace overlay or another Lean module.
The source module imports the public module by its canonical name.
Publication became visible during preparation. Its live bytes exactly match the checked source hash.
STATIC-CHECKS.json records whether publication was visible at freeze time.

Static checks compare every initial parameter and the full resource conclusion with the existing producer.
The checked dependency was used as text to verify the local import graph. There is no local import cycle.
No compiler, Lake, Nix, Git, board, heavy job, or subagent was used for this packet.
Static checks do not establish Lean elaboration or axiom closure for this new proof.

Scope remains open: this local pointwise theorem does not supply the initial prefix inputs at every worker budget.
It does not prove inclusion of partial stopped scan/callback outputs in a larger successful worker observation.
It does not prove one finite common original-root accepted term and assignment, parked backward completion,
or the full original typing, LPO, language, stream, count, weight, rank, and compiled-Haskell clauses.
