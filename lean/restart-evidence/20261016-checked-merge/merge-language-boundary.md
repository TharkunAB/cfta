# Merge selection and the current source predicate

Read-only source check, 2026-10-16 08:35 CEST.

The literal subsumption branch checks `edgeConstraint wide == noConstraint` in `cfta/src/Data/CFTA/Interned/Operations.hs:670-673`. The current checked merge graph should therefore specialize its generic `clear` parameter to equality with the canonical Top constraint. `SourceMemoGate.plain` is a different predicate. It checks that the combined source equality accessor returns `some []` and that the normalized positive guard exists (`SourceMemoGate.lean:24-26`). It can accept constraints whose syntax is not the literal Top record. A language implication does not establish equality of these Boolean branch decisions.

The independent semantic interpretation for the current inventory is `SourceEqualityPCSGuard.holds`. Literal Top truth follows from `holds_exact` and the empty equality and Top guard cases. The generic merge language theorem's `clearTrue` premise is thus unconditional for a literal equality-to-Top specialization. Its `topTrue` premise has the same proof. No universal conjunction law is needed by a target projection or a merge call.

The alternate `plain` predicate also implies independent PCS truth: use `PCSGuard.positive_source`, the positive support from `positiveNormalized_support`, and the empty source equality accessor. This does not identify the source subsumption test with `plain`. The public-indicator theorem `ConstraintConstructors.plain_true` has a separate `ActiveOption` representation premise. Existing physical `FieldAvailable` receipts derive this premise at resident fields. It must not be silently assumed for arbitrary raw constraints.

Projection retains each original row guard and equality-operation state. Proper projection drops ancestor guard tests, so its semantic theorem is selected-subterm inclusion. Its root branch has exact union language (`SourceEqualityProjectionAPI.forest_root`). General proper-path language equality with subterms of accepted originals is not claimed.

The checked merge lift still needs same-cache availability of each actual emitted field. In particular, a large group can emit Top. `ConjunctionFieldAllocation.empty_field` establishes this only at the operation state returned by the literal allocation. A memo hit or small group must not gain a fabricated allocation. Source allocation callbacks, lazy CAF evaluation, native identity correspondence, and pending memo publication remain runtime adapter boundaries.
