# Current native physical payload mass

Reviewed on 2026-10-17 at 06:54 CEST. No material defect was found. The production source has 110 lines and SHA `f3c75004cc84f76ac9c086c35450ec91397fb446d5d039c5747e92454bd88ea4`.

The module is generic in Symbol, Guard, and native word width. It adds no equality, semantic, closure, ordinary-only, or idle-table premise. Its eight public declarations are `NodeMass`, `EdgeMass`, `node_cell`, `edge_cell`, `initial_cells`, `read_bound`, `edge_read_bound`, and `resident_children`.

`NodeMass` bounds both captured original operands in every phase. A returned cell also bounds its exact returned value. `EdgeMass` gives the same property for complete captured rows and a returned row. Suspended and evaluating cells retain the two original bounds. The predicates do not assume an enclosing query or body result law.

`node_cell state valid stored handle cell found` reads the actual present node cell. Physical validity supplies both operand availability proofs and returned availability in the returned phase. The current complete constructor store supplies each mass bound. `edge_cell` uses the corresponding complete resident row proofs. Both theorems cover arbitrary populated tables and all present cells, including cells not selected by a new key lookup. They need no future completion or desired result certificate.

`initial_cells state valid` derives its own `Stored (initialBound state.machine.heap)` from `valid.machine.1`, which is the current heap Facts. It then bounds every actual node cell and edge cell. This computed initial bound is not a claim that a fixed earlier heap bound survives arbitrary later allocation. Later calls must carry the actual produced store bound.

`read_bound` and `edge_read_bound` use exact successful current issued-map reads. Their successful read supplies the actual record-map witness. The store bounds that complete payload without an extra coherence premise. The theorems do not infer payloads from an absent identity or merely from an identity range. `resident_children` derives `1 + values children ≤ bound`, strict child-list length below the bound, and strict full mass of every child. The proof uses complete row mass and the literal ordered list. It does not replace complete children by identities.

## Imported integration

`constructed_node_warm` constructs an ordinary source node containing an actual recursive Mu and a separate ordinary leaf. It adds a resident row with two occurrences of the constructed root. Source construction derives its own Facts and available root. Empty native tables derive physical validity. Actual lookup publishes node handle zero, demand changes its phase to evaluating, and finish installs the known available root. The kernel checks the actual cells in all three phases, all three produced mass predicates, the computed initial-bound corollary, and exact warm lookup and demand at the unchanged returned state. The table has one cell.

`constructed_edge_warm` starts from that completed nonempty node table. Actual edge lookup, demand, and finish produce a returned edge cell while retaining the populated node table. It checks all edge phases, their mass predicates, exact warm lookup and demand, successful current edge readback, full row mass, the exact two-child width, every child mass, and final physical validity. It derives the store bound from the actual constructed heap. No initial Facts, successful query, result law, or intermediate store bound is supplied to either kernel.

These are physical memo lifecycle kernels. Finish installs an actual available value or resident row from the fixture. The kernels do not assert that a native compiler body produced that result or prove a semantic intersection law. Their assertions match the physical premises of this module.

## Validation and scope

The absolute-path production strict check exits zero with an empty `physical-mass-direct-1.log`. The canonical target build completes 1177 jobs. Its only warning is the inherited unused `inputs` binder in `InternedFreshOrdinaryClosedCompletion.lean:24`. Final imported public checks are in `physical-mass-public-1.log`: eight full explicit axiom and signature pairs. Final integration checks are in `physical-mass-kernels-4.log`: two pairs. Both imported checks exit zero with no warnings, errors, holes, truncation, or nonstandard axioms. All failed evidence attempts and raw logs remain unchanged. Attempts 1–3 had evidence-only elaboration and concrete-key proof errors. Attempt 4 passes. The production source never changed after its first strict pass.

Mass ignores key metadata, identity values, symbols, guards, cached depth, and free-name fields. It includes the complete Mu body and both probes. This result bounds each payload and resident child list. It does not bound the number of native cells, total table mass, domain or equality caches, generated request count, future constructor growth, or complete recursive-query resources. It changes no Haskell code and establishes no new Haskell defect.
