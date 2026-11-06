# Actual callback and original-input progress obligation

The two model workers are `MicroCFTA.EnumerationState.enumerateOut`
and `MicroCFTA.EnumerationState.enumerateFully`.
Their complete preceding Source context was restored in check 487.
They use a Graph-parameterized Lean model.
Their optimized interned runtime realization remains unproved.

The first dependency is the exact native heap lookup/view operation.
Its contract must connect actual node IDs to
`MicroCFTA.EnumerationState.Node`.
No canonical implementation ID for that operation is established here.

The required callback obligations are:

1. Realize `MicroCFTA.EnumerationState.Graph.node` with faithful lookup.
   Bound nonrecursive descent from the original inputs.
2. Realize `MicroCFTA.EnumerationState.Graph.intersect` with the fixed
   native intersection operation. Preserve original-input key coverage
   for its results and all subsequent node views.
3. Prove that both uses of `MicroCFTA.EnumerationState.Oracle` preserve
   this coverage and the lineage history used for recursive progress.

`MicroCFTA.EnumerationState.intersectValues` consumes the intersection
slot. It does not identify a concrete heap implementation.
The current callback types do not supply the required preservation laws.
The Oracle interface permits state updates without those guarantees.

First identify the exact existing implementations and their contracts.
If an adapter is required, write the Lean realizer and its refinement proof.
Then derive the progress laws for those fixed implementations.
Do not introduce a supplied realization, carrier, closure, resource, fuel,
success, or validity premise.
A finite recursion-key set alone does not bound the work between checkpoints.

The full target remains one computable bound from the original inputs and
requested size for both actual optimized workers and all generated states.
It also includes exact accepted terms by node count, counts, enumeration
order, both rank/unrank inverse laws, and Haskell/runtime correspondence
for IDs, caches, interning, equality, and hashing.
