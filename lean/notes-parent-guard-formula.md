# Parent open-guard formula translation

`ParentGuardFormula` follows `targetTerm` and `partFormula` in
`Gen.Refinement.Internal.Compile`. It uses `DefiningTerm.termOf`, which
executes the source `onlyPoint` query before syntactic defining-term
extraction. The fallback expression must exclude the refined value variable.

`targetRefinement` reads the parent at `[]` or one immediate child at `[i]`.
A missing child observation or a deeper path has no target measure.
`renamedRoots` applies the actual child offsets and `renameFrom` replacement
tables. `renamed_child` proves the resulting child lookup, and
`renamed_refinement` gives its exact simultaneous-substitution environment.
The model uses the existing natural-number path representation. Signed
machine path conversion remains a source representation boundary.

`partFormula` supports `Satisfies` and `Holds` only. It preserves the original
guard in `IntegerLeafRead` errors. A failed checked formula substitution is
represented separately. In Haskell, that failure is the total substitution
wrapper's exception; it is not an ordinary empty-language result or a new
returned `GenError`. `partFormulas_first_error` proves left-to-right error
precedence for the source traversal. Unsupported guard forms are not silently
reinterpreted.

`substitution_values` proves the mathematical actual-value interpretation
of checked simultaneous substitution. It includes the source identity-entry
filter. Distinct formal names make removing identity entries semantically
neutral. The proof derives distinctness of the actual decimal-indexed
`contractTermName` names. Target paths may repeat. Each repeated path uses
the same actual value at its distinct positional formal.

`target_independent` derives value independence from the repaired caller
check. `target_exact` derives that each accepted refinement admits exactly
the extracted value in every ambient environment. It does not assume target
satisfiability. The public syntactic `definingTerm` extractor still accepts
`v == v`; the two generator callers reject that fallback.
`target_value` identifies a supplied refined value with the extracted value.
`literal_roots_exact` obtains the required evidence for canonical filled
integer labels from the actual singleton reader.

`partFormula_exact` proves that a successful translation holds exactly when
its guard holds mathematically on those exact target values.
`actual_satisfies` identifies this interpretation with implication from the
filled singleton refinement. `Holds` uses the complete positional actual-value
assignment. `partFormulas_exact` composes the ordered guard list, and
`parent_formula_exact` joins it with `ParentIntegerSettlement`'s actual
child-formula fold.

`partFormula_target` derives successful extraction at every requested path
from the actual dispatch and ordered lookup. `partFormula_derived` then
proves exact guard meaning at those extracted values with no refinement
truth or independence premise. `satisfies_entailment` identifies the result
with mathematical implication from the actual observed target refinement.
The accepted target cannot use inconsistency to entail every condition.

The mathematical statements do not equate an arbitrary solver's `Yes` or
`Unknown` result with truth. Complete observation transport, root-label construction, and the
selection of open guard parts remain caller interfaces. The separate
`DefiningTerm` module proves extraction and coordinate-fill provenance.
This module does not prove those complete compiler record invariants.
The related two-caller source repair and its public counterexample are in
`notes-self-dependent-measure.md`.

Validation: `lake build MicroCFTA.ParentGuardFormula` succeeds with the pinned
toolchain. All 31 theorem audits report only standard Lean axioms. The module
has no added axioms or incomplete proofs.
