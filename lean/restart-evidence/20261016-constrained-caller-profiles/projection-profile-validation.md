# Actual projection profile validation

Validated: 2026-10-16 19:40 CEST.
Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.lean` (277 lines).
Source SHA-256: `d2a9fe2a28b16b916ac538b51d6c6ad188d56e9efc7f3e220cdab4dc3d88cd37`.

The module proves profiles and height bounds for the same supplied Project, ProjectRows, and Forest graphs. It derives all smaller profiles by the mutual graph recursor. The public endpoints have no result-profile, recursive callback, future readiness, or completed child premise.

`projectRows R depth` is `(max 1 R)^(depth+1)`. Each ordinary projection level unions at most one returned node per original row. `rows` derives the returned ordered ChildrenShape, result count at most the literal input row count, and child-height maximum at most the original row-height maximum. `union` accounts for concatenation with row limit `max 1 values.length * R`; it retains the input maximum height. Source root union and signed missing/selected positions remain separate. `forestRows R count depth` is `max 1 count * projectRows R depth`. `project_uniform` and `forest_uniform` expose explicit initial row/arity/height, forest-count, and path-depth bounds.

`read_exact` and `readAll_exact` prove literal nodeEdges/flatMap row readback and unchanged heaps for finite ordinary input records. Actual union uses the new constructor law, including coherent cache hits. Initial SemanticReady, resident rows or available inputs, and supplied input profiles justify every reached physical read. The input profile derives the finite ordinary domain. Actual prefix physical effects and availability come from the existing Projection theorem on the same graph and endpoints.

Validation:
- Direct source: `projection-profile-direct-3.log`, terminal exit 0, no diagnostics.
- Canonical target: success entry `[1121/1122] Built MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionProfile` in `projection-profile-reservations-build-1.log`. That batch failed only on the separate root-owned ProjectionReservations target. This is not recorded as a successful whole batch. The subsequent reservation repair batch completed successfully in `projection-reservations-build-2.log` (1119 jobs).
- Fourteen public axiom/full-signature pairs: `projection-profile-public-1.log`, exit 0.
- Four imported integration pairs: `projection-profile-kernels-2.log`, exit 0, no warnings, errors, or `sorryAx`.

The kernels construct a literal forest-root union from finite original row reads and its own makeNode return; construct a first-child graph followed by its actual singleton union; prove a negative forest position returns Empty at the unchanged heap without source inspection; and compose two supplied projections using only the first returned profile, availability, and SemanticReady for the second input. The last kernel has no independent second-state invariant or second-input profile premise.

This is a profile and height component. It does not count constructor requests, establish cumulative capacity, prove projection worker completion, prove merge result profiles, or close the Haskell runtime schedule boundary. Counter accounting remains in the separate root-owned reservation module. No older source, Haskell source, Audit, root documentation, or prior evidence was edited. No Lake command ran here. Earlier failed source checks and the first warning-only kernel log remain diagnostic evidence.
