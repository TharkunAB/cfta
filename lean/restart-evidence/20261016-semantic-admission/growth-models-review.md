# Read-only review of input view growth

Date: 2026-10-16 07:19 CEST.

Reviewed `SourceCurrentAllocatedNativeInputGrowthModels.lean`, 167 lines.
Frozen source SHA256:
`632c37e10a6a0067244baeeb98cd28f1b6b8eee7ffe3814cbb99a8f977112a5a`.
No proof source was edited. No canonical Lake build was run for this review.
Root supplied the focused GREEN460/build-3 result.

No material defect or hidden result-law premise was found.

- The mutual structural recursor transports the same input, rank, and term.
  Node rows retain the same guard function. Binder/reference strict rank
  bounds and union/forest weak bounds are retained unchanged.
- The reference case uses FiniteInput.reference_valid to admit the Mu tag
  before applying body closure. ViewAgreement alone would not supply this
  reference closure. The extra premise in the private forward lemma is
  discharged by the actual finite interface in both directions.
- reverse_agreement remains on the old valid domain. Its body, row-child,
  and union-member closures rewrite after-view reads to before-view reads.
  It does not infer agreement at unused identities.
- lift keeps the exact old valid predicate and representative definitionally.
  identity_exact and reference_valid therefore remain valid. The new-view
  body/row/member obligations follow from their retained old reads.
- lift.copy_exact derives old closedness from retained free metadata. It
  rewrites the copied syntax to the old copy, uses the old independent copy
  law, and transports each exact finite rank in the required direction.
- lifted_rank proves an iff at the same natural rank. lifted_language only
  erases that same rank by existential quantification. Neither theorem
  weakens exact rank to an unrelated bound.
- inventory_agreement gets OriginalInput for every admitted old input from
  actual reachability from listed closed Original available roots. It then
  uses retained issued-map history and physical payload growth. It does not
  assume global closure of all syntactically Original available values.

Scope remains correct: this component lifts an old model through physical
heap growth. It does not add projected or generated operand identities.
It does not by itself transport contextual warm-cache laws or prove a new
query. Inventory extension and contextual cache rebase remain separate.
The fixed holds function is unchanged on both physical views.

## Standalone checks

Pinned Lean 4.34.1 `lake -d lean env lean` returned terminal 0, no warnings.
Six public declaration axiom probes and six signature checks passed.
All probes use only propext, Classical.choice, and Quot.sound.
Three kernel examples check unchanged valid domain and representative,
reference-to-Mu closure, and exact old-valid reference rank equivalence.
Raw files: `growth-models-review-probes.lean` and `.log`.

## Reviewed hashes

```
632c37e10a6a0067244baeeb98cd28f1b6b8eee7ffe3814cbb99a8f977112a5a  lean/MicroCFTA/SourceCurrentAllocatedNativeInputGrowthModels.lean
b9f0b2e39416caa31cead16602f1014232b92d7aaeaf3c6b33d67d71e55dfa16  lean/MicroCFTA/IntersectInput.lean
ec166d86dcadc8d8d28de8c7be2c6e7726307267cb69b1ad305d84f224ed7aaa  lean/MicroCFTA/IntersectViewAgreement.lean
67deb446edf59dbc1869f75e130ee8ad93e0772f852b1b37bc37c3cf7245ce51  lean/MicroCFTA/SourceRecursiveIntersectionScheduleGrowth.lean
51977557d8d6cd3b2cbd0da970192062a120408aa20d79e5376cd341a902f5b3  lean/MicroCFTA/SourceRecursiveIntersectionInputGrowth.lean
7c4f83cf02014d7046a46f5099c283f66fa93931660b22d746bbac198648bb6e  lean/MicroCFTA/SourceCurrentAllocatedNativeInputInventoryModels.lean
```
