# All-phase native request admission

Date: 2026-10-16 07:35 CEST.

Source: `SourceCurrentAllocatedNativeAdmissionCache.lean`, 204 lines.
Final frozen SHA256:
`7d56d8e6116cf35dff25bbf99b3d821c6ae883a67e07fddcf43ea041afd9755b`.
Only this new proof module and new evidence files were edited for the task.

## Validation

- Initial isolated pinned Lean source check passed. Its first log records
  unused lambda names. The corrected direct check has no warnings.
- The additive Covered.rebase theorem passed direct Lean with no warnings.
- Root reported final canonical AdmissionCache+Execution+Code GREEN1087,
  terminal 0. The updated AdmissionCache olean includes the final rebase.
- Standalone public probes passed, terminal 0, no warnings.
- Eighteen public theorem axiom reports passed. They use only propext,
  Classical.choice, and Quot.sound.
- Twenty-two full signatures passed, including the four invariant definitions.
- Twelve kernel integrations passed. They cover empty caches, actual hits
  without candidate admission, suspended and evaluating cells, finish,
  lookup-then-demand, both returned-cell projections, machine advance,
  and cross-view rebase of returned and evaluating cells.
- No placeholder or project axiom is used.

Commands used the pinned Lean 4.34.1 toolchain. Direct source checking used
`LEAN_PATH=lean/.lake/build/lib/lean` and wrote only an isolated evidence
olean. Public probes used `lake -d lean env lean`. No independent canonical
Lake build was run while root or another worker owned that build slot.

## API and scope

`Requests property table` covers every physical cell's original request.
It has no phase restriction. Requests.lookup inserts only a supplied covered
request and retains a hit unchanged. Requests.status/demand/finish retain the
same stored request. They do not assert candidate result semantics or result
residency, and do not replace physical cache validity.

`NodeCovered inputs request` is NodeInputs in the finite input model plus
SeenCovered for the request domain. EdgeCovered uses both ordered child lists
and the same seen-name coverage. `Covered inputs native` has nodes and edges
projections for all cells, including suspended and evaluating cells.

Lifecycle lemmas derive initial, advance, lookup, demand, and finish coverage.
`Covered.admitted` and `.seen_admitted` derive the weaker invariants on the
same actual returned cells. `Covered.rebase agreement` transports coverage
of every same cell across derived old/new inventory Agreement.

`node_published` and `edge_published` identify the exact stored request using
physical cache validity, actual published key/cell receipts, physical ready
operands, and checked keys. Word-range requirements occur through those
checked key receipts. Pure request-property preservation needs none of these
extra key assumptions because it does not identify different requests.

## Remaining obligation

The module establishes the cache lifecycle invariant. Actual source code
must still derive NodeCovered or EdgeCovered before each new request lookup.
Root AdmissionExecution supplies actual finite reached checks; source branch
certificates and physical trace simulation must derive those checks for a
complete query. No new result-language law or general query completeness
claim follows from request coverage alone. Runtime publication, machine-key
identity, and source initialization remain the existing adapter boundaries.
