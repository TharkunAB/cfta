# Move the verified callbacks to their existing owner

PROPOSAL ONLY. No live Source file changes. No compiler or Git operation.
All three public theorem headers and proof blocks compare byte-exact.

Move the two complete callback namespace bodies to the end of
SourcePruningEnumerationSharedEagerReservation.lean, after its final namespace
end. OWNER-APPEND contains the exact bodies in dependency order. A surrounding
section scopes autoImplicit=false. The moved namespace bodies remain unchanged.
Replace each of the two former files with its supplied one-import wrapper.
The wrapper modules keep ordinary imports and expose the same public QNames.
Remove their old theorem bodies when applying this move. Do not retain copies.

The owner already imports every other prerequisite of both bodies transitively.
No owner import is added. Neither callback body has a private declaration.
No private helper changes visibility or module ownership. Existing private task
helpers stay in the owner and become usable beside the proven public callbacks.
The imported callback theorem names and statements remain identical downstream.

DAG-REPORT records actual prerequisite paths and absent return paths. The proposed
wrappers point to owner. Owner never points to a wrapper. This removes the cycle
that would arise if owner imported the former callback implementation files.

BYTE-COMPARISON checks all three complete public headers and all three complete
proof blocks against live verified Source and proposed owner append. Source pins
record the exact three inspected files. The proposal makes no semantic change.
Root must run normal dependency builds and strict public/import checks after
applying it. No proof credit is claimed for this uncompiled relocation proposal.

The new generic source task proof can then stay private inside the owner. Reuse
the existing untyped frame/task data, work and forecast definitions. Parameterize
runtime callbacks/run/root_visit over generic metadata and the literal real hook.
Generalize the ledger/current/result metadata typing while retaining original
past tuple histories. Keep old Unit/identity APIs as exact specializations.
The move does not itself prove nonempty tuple histories or the full real worker.
