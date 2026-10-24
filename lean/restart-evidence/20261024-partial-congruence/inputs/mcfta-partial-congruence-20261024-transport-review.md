# Partial-render transport candidate self-review

Reviewed 2026-10-24T02:30:57+02:00. Status: SOURCE_REVIEWED_UNCOMPILED.

Personally read all154 candidate lines after adding the exact existing List law proof with a distinct instance name. The pre-lawful137-line draft is retained separately. This note records the author's own review, not an independent mathematical review or kernel acceptance. No compiler/import/selected program was run. No repository or sealed checkpoint file changed.

The sole public theorem has the requested argument order: graph,leftFuel,fragment,left,right,leftAfter,term,frame,total,leftRender. Its premises are only Frame left right, Total left.representatives and ONE observed left Success. The conclusion constructs rightFuel/rightAfter with the SAME term and Frame leftAfter rightAfter. It has no right-success, desired-result, accepted completion, Safe, Finished, graph-validity or resource oracle premise. It does not depend on paired partial agreement.

Induction decreases the actual left render fuel. The node branch uses a local ordered-list induction, retains all source/right intermediate states, adds finite child bounds, and raises the two actual traversals with expandPartial_moreFuel/retains_mapM. The empty traversal uses bound0 and the enclosing node uses bound1. Child order and output multiplicity are retained. There is no new state machine or observer predicate.

The enumerated-hole branch first constructs the matching read with getValue_transport, then transports the actual finite stored-fragment render. It chooses readFuel+tailFuel+1. getValue_moreFuel raises the read to that outer bound; expandPartial_moreFuel raises the recursive render to its predecessor. These raises retain identical after states. Totality at each left continuation comes from the actual read/render's complete frame.

Terminal cases choose readFuel+1 and keep the same original hole ID. Only an empty-suspended recursive boundary truncates. Nonempty suspended constraints, absent nodes and eliminated slots remain holes after a successful value read. No missing slot is fabricated, and no unconditional partial termination or equal-fuel claim is made. Both local instance names are explicit and distinct. The LawfulMonad List body is byte-identical to the existing EnumerationUntilBridge law body after its one declaration-name substitution.

Dependencies: installed EnumerationPartialObservation imports the existing primitive observations and Execution APIs. Used getValue_transport/getValue_frame; expandPartial_frame/moreFuel; Frame.total; success_bind/success_pure/success_failure; List.mapM_cons; retains_mapM; and getValue_moreFuel. No additional library import or new helper declaration.

Checked source identities:

| Input | Bytes | SHA256 |
| --- | ---: | --- |
| `/tmp/mcfta-partial-congruence-20261024-transport.lean.txt` | 9533 | `aee95131327723f0e757b69aa2e9fcea9f7a30b67dc1db0b8daf0e6aee5fbdd0` |
| `/tmp/mcfta-partial-congruence-20261024-transport-before-lawful.lean.txt` | 8855 | `e5ddf857a3952d50ea11e6482d4bfdb80929d5b57f470be703bf59e134c85e71` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationPartialObservation.lean` | 4692 | `e407fa36087e6f5521dbd2da098aa49d1fe37817f16a2c9d32227d56153e67bc` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationObservations.lean` | 6136 | `ebc891e8461c7b545d55f6823322789f19635e2d1c58a5551307b621079ba0ab` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationState.lean` | 33489 | `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationExecution.lean` | 30176 | `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationUntilBridge.lean` | 14619 | `ac5eb73483f5d59bf52f1a251c55322050f289cc8a9dd052d032ab8e32638642` |
