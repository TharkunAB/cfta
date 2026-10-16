# Read-only review of recursive request admission

Reviewed `SourceCurrentAllocatedNativeRequestAdmission.lean`, SHA256
`2889fc2981569a36f9d5dc414045e72b6a276f9dc46aee12e4460cce2aba48f0`.
No source edits or independent build were performed for this review.

No material defect was found. Admission comes from the parent input
predicate and exact physical readback. No child result, parent output law,
completed recursive call, or future cache invariant supplies it.

* Domain changes and swaps preserve exactly the original ordered operands.
* Union membership is rewritten through literal source union readback
  before `model.union_valid` is used. Original child scope comes from the
  actual parent scope and the same member occurrence.
* Ordinary row admission uses literal `Kernel.pairs` membership.
  Child admission uses actual zipped children. No arity premise is needed
  for the admission of each zip member; rejection and complete child-list
  selection remain responsibilities of the checked edge body.
* `body_inputs` uses `body_encoded` and the model's actual Mu-body closure.
  Non-Mu operands remain unchanged. Its arbitrary entered domain does not
  weaken the statement: `NodeInputs` is independent of the request domain.
* `entered` derives source scope at the actual returned interned domain via
  `entered_key`. It does not claim seen coverage from arbitrary numeric
  pair arguments. PairAdmission supplies that separate obligation from
  actual successful operand identities.
* `resolved` combines `OriginalBindings.read` with the literal current
  `read = some bound` receipt. Option injectivity identifies the exact
  original binder record. It retains `Available source bound`, and parent
  reference admission derives Mu input admission through
  `model.reference_valid`. The left/right wrappers preserve operand order.

Source `Facts` remain necessary for original row-child and body readback.
Current heap facts alone do not establish availability backwards in the
fixed source heap. The module keeps that distinction explicit.

The scope is local admission closure in one fixed source model. It does
not establish every stored cell's admission, finite native execution, a
result-language law, generated-query history soundness, or runtime GHC
publication and forcing. The header states this boundary accurately.
