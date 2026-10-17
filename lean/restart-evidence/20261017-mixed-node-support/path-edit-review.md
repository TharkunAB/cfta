# Positional edit support component

The final production source is `SourceCurrentConstrainedCapEditSupport.lean`.
Its SHA-256 is `915381224c3ac7251d2105731d3c8d34a2706504452467bec4457fe68ac6208a`.
It has 605 lines. Strict direct attempt 12 passed with an empty log. The
canonical build passed 1345 jobs in `edit-support-build.log`.

`AtLeaves` checks the immutable original node at every retained callback
path. `ChildrenAtLeaves` uses the literal signed lookup and scan offset.
`class_placement` uses the actual compiler leaf permutation and the coherent
class's prefix separation. It supplies no returned-node assumption.

`Preserves` quantifies over every original supported path. The ordered child
relation therefore covers disjoint paths and both strict-prefix directions.
The actual edge helper retains the complete raw guard and the ordered child
relation. The actual node helper follows surviving canonical rows, including
cache readback. `head` derives its own path law from the actual Head graph,
initial local Cap, MuStored, readiness, closedness, and availability.

The four `*_with_leaf_certificates` endpoints are CONDITIONAL algebra. Their
`NodeLeaves`, `ChildrenLeaves`, `RowsLeaves`, and `ListLeaves` premises require
`LeafCertificate` for reached leaf events of the supplied graph. Each event
retains its input and complete before/after shared states. The certificate
states that an annotated original input and initial Mu store give the actual
annotated result and returned Mu store. It is an explicit remaining leaf
producer obligation. It is not derived from arbitrary warm native tables.
The proof derives all intermediate Ready states and constructor facts from
same-prefix Reads and existing physical effects.

The imported probes check all 35 public declaration commands. Three
integration kernels construct an actual Head, execute the original negative
slot behavior, and compose literal raw-edge and raw-node work with an
arbitrary nullary raw guard. The negative-slot kernel constructs its own
strict Reads and has no actual leaf call. The constructor kernel derives
its intermediate physical readiness and has no returned mask premise.
All final checks pass with standard Lean axioms only.

The raw graph relations are propositions. These results are logical
same-endpoint graph certificates. They do not identify host forcing events,
HashMap iteration, or the operational publication schedule in GHC.
