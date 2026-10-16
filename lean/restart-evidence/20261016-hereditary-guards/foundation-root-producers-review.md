# Independent review of the guard constructors and graph producers

Date: 2026-10-16 22:58 CEST.

No material defect was found in the three frozen sources below. This review checks the proof inputs, the actual intermediate states, and the stated source boundary. It does not repeat the owner's public declaration probes. No source was changed. No build or Haskell command was run for this review.

## Literal constructor results

`SourceCurrentAllocatedFiniteOrdinaryGuardConstructors.lean:60–76` proves the bound for the actual returned edge. `makeEdge_key` supplies the complete requested key. `makeEdge_children` supplies the complete requested child list. Both facts use the same literal constructor run. Their coherence, cache, and child availability inputs justify cache hits as well as allocations. The proof does not infer complete returned records from reference equality alone.

`GuardConstructors.lean:79–95` proves the bound for the actual returned node. The proof first filters and canonicalizes the supplied rows. It derives residency for each selected row from membership in the original rows. `identifyNode_readback` then identifies the complete rows of the actual returned node. The empty result is handled separately. Filtering and canonicalization retain the hereditary bound. The proof does not require a bound on the returned profile as an input.

The ordinary union endpoint at lines 106–114 uses these same literal constructor facts. These endpoints prove hereditary profiles. Their conclusions do not assert allocation counts or complete physical state invariants.

## Signed projection graphs

`SourceCurrentAllocatedFiniteOrdinaryGuardProjection.lean:24–41` follows the supplied union graph. `readAll_exact` proves that its ordinary read returns the literal flattened source rows and retains the heap. The proof rewrites the actual constructor equation with both equalities. It uses the original forest's availability and the initial linked heap to derive residency of those exact rows.

The projection recursor at lines 62–101 uses physical facts from the same actual earlier prefix. Each selected child comes from the actual signed lookup. Its initial availability follows from the resident original edge. The prefix's `Keeps` fact transports the remaining original edges to the actual next heap. The ordinary domain excludes the recursive-head branch; the proof does not assume a head callback law.

The public `project`, `rows`, and `forest` endpoints at lines 113–137 retain the same bound vector. The forest cases include root union, missing selection, and successful selection. They verify supplied completed graphs. They do not construct finite projection execution.

## Required-path graphs

`SourceCurrentAllocatedFiniteOrdinaryGuardRequired.lean:48–58` rebuilds the actual node at the heap returned by the supplied row prefix. The physical row theorem and the hereditary induction hypothesis apply to that same prefix.

The selected child case at lines 76–88 transports unselected source children through the actual earlier child return. The kept row case at lines 97–127 retains the original raw constraint. It uses the actual rebuilt children at the actual middle heap. It transports the remaining source edges through both the child prefix and the literal edge constructor. It does not omit the constructor's heap growth.

The recursive-head case at lines 59–65 is impossible under the initial hereditary ordinary profile. Unselected children and rejected rows retain their original bounds. No closure premise for unrelated siblings is added.

`requireAll_done` at lines 172–182 converts the supplied literal worker success to the graph for the same compiled required paths, output, and heap. It then applies the graph result. This endpoint assumes the literal success that it verifies. It does not assert general required-worker termination.

## Source and model boundary

The source projection cases are `cfta/src/Data/CFTA/Interned/Operations.hs:787–792` and `:813–814`. They distinguish root union from child selection. The source required traversal is `cfta/src/Data/CFTA/Equality/Operations.hs:279–303`. It preserves each retained row's raw guard while it changes children. These are consistent with the properties proved here.

The projection and required graph paths use signed indices. Successful lookup supplies actual membership. The raw equality paths in `GuardEnvelope.Bounds` remain the preserved natural-index constraint model. The new theorems do not identify that model with all signed Haskell constraint conversions.

The hereditary domain excludes Mu, explicit union, and references. The proofs use generic `Symbol` and `Formula` with raw `SourceSymbolicIndex.Constraint Formula`. They do not prove general recursive completion, a whole-caller resource plan, solver completeness, GHC demand order, or HashMap event replay. No Haskell defect is established by this review.

The accompanying reviewed-hashes file pins the reviewed sources and the relevant immutable dependencies. The owner's canonical results are Constructor 1083 jobs and Projection/Required 1155 jobs, each with terminal exit 0. This review does not claim those build runs as independent executions.
