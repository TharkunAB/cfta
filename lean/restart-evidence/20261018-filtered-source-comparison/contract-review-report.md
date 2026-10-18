# Filtered source contract boundary

Checked on 2026-10-18 at 19:37 CEST. This component adds evidence only. It does not change a production module.

Two public existential witnesses pass the pinned Lean 4.34.1 kernel. The selected strict source is `contract-review-kernels-1.source.lean`, SHA256 `cc7c8a270e6380e51e9b4fc4e0ae566ad88cf65a8f39a6c3d0c4b8f98fea2a64`. Its log has zero bytes. The full two-head probe is `contract-review-public-1`, source SHA256 `f22710f52f1e071cb33fa096c5d44d08180caddda9cc10ecfe0595bec9cf6f50`. It prints each exact statement, complete public proof, and axiom report with all eight required options. The hardened checker accepts only the three standard axioms and rejects omissions, printer failures, errors, and warnings.

## Actual source boundary

`FilteredProfileContractBoundary.actual_source_filter_boundary` retains two literal successful source calls from empty caches, in sequence. Let `x = uninterned 10`, `z = uninterned 11`, and let `N` be the ordinary row with symbol 7, guard false, and ordered children `[x,z]`. The first source returns `A = union[x,N,rawMu(z)]`. The second returns `B = rawMu(union[x,z,N])`. Both Mu constructors use the raw form, so the unused binders remain present.

For every profile assignment, the complete stored denotations of A and B are equivalent. This uses the full encoded plans. It does not infer the result from their original opaque root profiles. The actual original root filter at x removes the bare x member from A. It leaves the root Mu B unchanged. At the assignment `x -> some [uninterned 30]` and `z -> some []`, filtered A denotes Empty and filtered B denotes the reference 30. The original source expressions differ. This witness alone is not a same-expression source comparison counterexample.

## Resident summary boundary

`FilteredProfileFullBoundary.correct_does_not_control_filter` constructs actual source probes for an outer source expression which ignores its own local reference. Those probes have the shape A. It reserves their actual outer key, constructs B as a separate actual source body under the reservation, and completes that outer record with B as its payload. This last pairing is an artificial cache payload. It is not a source publication of that outer expression.

The public witness derives all of the following at its exact reader: joint `Context reader []`, `Ready reader`, complete resident availability, the existing profile/free/depth `Correct` facts, the new parametric `StoredMuProfileContract.Correct`, and `PublicationHeapInduction.Heap Correct reader` for every resident Mu. The last fact follows by a finite classification of the actual record table. The body and probe still have different actual filtered denotations at x under the assignment above. The proof includes both old smart and raw depth observations, including exact deep-name membership.

Thus the new unfiltered `Correct` contract does not imply arbitrary root-filter agreement between its body and probe. It still supports its stated unfiltered execution theorem. No claim about that theorem is refuted here.

## Remaining contract question

The proposed universal common-reader source law is not refuted by these public statements. A complete refutation would also require two actual builds of the same syntax, exact live compatibility and alias/self tests, both historical growth and issued-extension receipts, and the specified warm filters in one reader. Those premises were not assembled. Renaming the second capture pair can avoid conflicting same-key payloads, but that observation is not a checked full-law counterexample.

The evidence establishes a local obstruction to deriving the proposed filtered law from unfiltered parametric cache correctness alone. A stronger invariant may need to retain the original root alternatives or suitable filter-parametric behavior. Proving the actual source publication invariant remains separate work. This component makes no runtime or Haskell defect claim and no general completion claim.

## Preserved attempts and scope

The first pure attempt left profile case splits and the final negation open. Its second attempt passed with a zero-byte log. The first full draft copied older fixture infrastructure and still contained obsolete execution equations. Later attempts repaired only proof syntax, membership normalization, and finite table proof cases. The fourth full attempt also exposed an unused simp argument. All sources, logs, limits, and receipts remain unchanged. The fifth full intermediate passed. The final combined two-head strict attempt and its public probe passed without warnings.

All nine owned checks used the copied runner with 4 GiB memory maximum, 4 GiB memory high, zero swap, and a five-minute time limit. No production source, older evidence, Audit, authority document, Haskell file, or Git state was changed. This evidence-only fixture has no separate production canonical target. Counts: zero production heads, two constructed heads, zero auxiliary heads, and zero reused proof pairs.
