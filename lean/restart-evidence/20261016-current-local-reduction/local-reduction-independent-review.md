# Independent local reduction review

Reviewed source: lean/MicroCFTA/SourceCurrentAllocatedLocalReduction.lean.
SHA256: 444f8bddf160f270a7756529edee316562c1cc5aab8ed692b6cd82d664f2272c.
The source has 174 lines. It was not edited during this review.

No material proof or source-scope defect was found.

The raw graph follows Operations.hs:207–211: unchanged for two empty equality payloads, erased children for contradiction, then the current Scan and required/class continuation. The live continuation starts at SourceCurrentAllocatedPrecheck.state before loaded inherited. That state has the entire original native state and exactly the operation state returned by the actual accessor and precheck. It does not reset operations. The constructor heap is definitionally unchanged by this prefix. Reuse of input residency, merge Stored, global validity, and fourth correctness in early branches is therefore justified.

The finite theorem derives the precheck from initial same-cache load, cached original normalization, inherited readiness, Good, and inventory At. It does not take a chosen successful branch. The actual classes return derives proper paths and coherent ascending nontrivial records. It then invokes the current ScanClassPass theorem from the literal precheck return. The range plan quantifies only over actual precheck classes output, followed by reached Scan and class-prefix plans. It does not supply a completed Scan, future readiness, target-model language, or final inventory.

The final Receipt.precheck stores its initial inventory existentially. Receipt.admitted uses the actual computed final inventory. These inventories are not equated. Native tables, equality operations, global bundles, fourth memo, and merge memo pass through the actual graph and its read receipts. The live branch composes precheck and continuation physical effects. It asserts no fixed native tables or fixed domain cache after native queries.

The language theorem uses the complete original PCS guard and inherited equality satisfaction. Contradiction excludes that conjunction. Live class satisfaction follows from original own equality satisfaction, which the full original guard implies. Ignoring inherited satisfaction in the live preservation proof is sound: the live records contain own classes, and inherited equalities serve the precheck contradiction test. The theorem makes no unconditional output equality claim.

For an empty child list, erasure returns the empty list. This forest still accepts the empty ordered term list. The contradiction branch does not assert otherwise. Its conditional language equality follows from the impossibility of full guard and inherited satisfaction together. Unchanged and live branches also retain the exact zero-child behavior.

Independent pinned direct Lean probes passed in local-reduction-independent-probes-3.log. They checked one public axiom report, five public signatures, and three separate integration kernels with reports and signatures. Total: four axiom reports and eight signature checks. All axioms belong to propext, Classical.choice, or Quot.sound. The final log has no errors, warnings, or sorryAx. Earlier logs preserve evidence-only reserved-name and proof-index inference errors.

The kernels check the entire unchanged native state plus literal returned operations, zero-child contradiction erasure with accepted empty forest, and a resident-edge entry. The resident-edge kernel derives the same-cache load and child availability from initial physical invariants. It supplies no separate Cached, load, class correctness, or future result law.

The source correspondence is completed serial graph correspondence. Haskell laziness, actual memo thunk publication, physical identity representation, and outer constrained fixpoint convergence remain separate adapters. This module does not prove them.

Reference hashes:

- SourceCurrentAllocatedPrecheck.lean: 3f4f770754e70986a50381edcff959d99209e45b590a94af547bf8477ab5f28c.
- cfta/src/Data/CFTA/Equality/Operations.hs: 5bf6e9b0f4033c11ac7723a17fe8d1b94d95a259187f0402285ad0147e439b09.
