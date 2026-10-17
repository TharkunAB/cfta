# A copied constrained child can be cold

The selected source is `SourceCurrentOuterCopiedCold.lean`.
Its only public theorem has no premises. It constructs its source from the empty physical heap.
It derives `Ready`, availability, closedness, and empty outer result tables from that construction.
It retains actual normalized equality allocations for every source guard.

The root children are `[tau, B]`. The plain productive Mu `tau` precedes the finite constrained node `B`.
The root equality is `[[0,0],[1]]`. The own equality of `B` is `[[0],[1]]`.
The first parent result contains a plain wrapper with children `[B,tau]`.
The exact literal `Reached` prefix goes from the root request at outer fuel 24 to the copied `B` request at fuel 18.
At that state, root owner 0 and wrapper owner 1 remain evaluating.
The copied request inherits the empty live payload, and its physical key is absent.
Its actual demand allocates owner 2 and chooses evaluation.
The copied call completes. The complete original root call also completes.
The final caller retains owner 2 with the exact full returned value `B`.
A replay of that request is ready at the same complete caller for all outer and lower worker fuels.

The theorem also proves that `RequiredRowOrigins.Origin tau copiedB` is false.
The actual gate proves all guards in `tau` plain. The copied value has a nonplain row.
The existing origin relation preserves the full guard at every nonplain row occurrence.
This contradiction rules out a provenance explanation that uses only `tau`.
It does not rule out an origin relation over the whole initial source: `B` is an initial sibling.

This finite witness refutes the proposed already-ready shortcut.
It does not prove divergence, a Haskell defect, or failure of every global origin order.
A general progress certificate must account for the pending external `B` dependency and its source order.
It must also distinguish this case from the earlier copied warm-hit fixture.
No future graph, rank, successful callback, or completed child is a premise of the public theorem.
The `Reached` relation records the exact literal branch prefix; it is not a new whole-worker success theorem.
The separate full root equation proves success of this fixture.

Selected checks are strict direct 3, canonical 2, public 4, and imported kernel 2.
The canonical build has 1776 jobs. It replays only the inherited ClosedCompletion warning.
The new source and printer-free imported integration have empty strict logs.
Direct attempt 1 and the preliminary exploration remain unchanged.
The final public proof print and imported axiom probes use all eight explicit options.
The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Public attempt 1 completed the signature and axiom checks, but its full proof printer failed.
Its raw source, report, and output remain retained. Attempts 2 and 3 terminated with exit -15. No cause is inferred from that code.
The selected source moves the unchanged finite proof into a private witness.
The public statement is byte-identical to the prior statement, and its proof is that witness.
This separates the complete public proof print from the finite calculation proof.
The new strict, canonical, public, and imported checks use this final source.
