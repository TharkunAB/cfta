# Independent review of actual prefix union normality

Reviewed source: `SourceCurrentOuterUnionNormalHistory.lean`, SHA256
`fea7a8a24685ae8bc39d183dffdee4e8c99147bdda8dfbdb4d80508a48ef5266`.
No material issue found. This review adds no Lean declarations or builds.
It reuses three public pairs and one constructed pair.

`reached` follows each literal `ExecutionAncestry.Step`. Node activation
changes the memo table and keeps the checked heap. The row-edge case uses
the actual completed `edgeCall` return. The row-tail case first uses that
return and then its actual completed descendants return. The walk-tail
case uses the actual completed child call at its literal descended entry.
The other steps keep the checked heap. The induction does not replace
earlier completed siblings with their candidate inputs.

`stopping` applies the existing all-outcome normality theorem to the exact
reached phase. The private `erase` lemma proves that erasing the successful
result does not change the outcome state. Failures retain their actual
state. This is preservation at a stopping outcome. It does not assert that
the reached phase completes or that every state in a failed call is idle.

`constructed` obtains initial union normality from the outcome state of
the literal closed constructor. Its entry equation is explicit. It does
not require a future whole-call result or physical Good, and does not
derive other semantic or resource invariants from union normality.

The checked fixture constructs a root with three children. It completes
the Parent edge and the first two siblings, then derives the exact third
child entry through `walk_prefix`. The new `constructed` endpoint supplies
normality at that entry and its stopping state. The fixture contains real
completed calls, rather than a reflexive prefix only.

The selected strict source is direct-3 and its log is empty. The canonical
receipt is canonical-2. Its only warning is the existing unused `inputs`
warning in `InternedFreshOrdinaryClosedCompletion.lean:24:5`. The selected
production probe is public-2; the selected fixture is kernels-direct-2 and
kernels-public-1. Both groups pass all eight printer options, full proofs,
explicit checks and the standard three axioms. Earlier warning attempts
remain unselected. No mutable root peaks or global metadata are pinned.

These results preserve a syntax invariant through actual bounded calls.
They do not bound renewal, exclude node-owner collisions, prove recursive
completion, or establish Haskell correspondence.
