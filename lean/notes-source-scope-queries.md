# Mathematical meaning of source nested queries

`SourceScopeStack.lean` records each successful source `resolveMany` call in
a stack of substitution recipes. The recipes contain actual source paths.
`transport` derives the second stack from equal guard reads. It preserves
resolution failure, entry order, scope order, and all non-formula metadata.
`closed` derives the finite live-name invariant from the resolved records.
These properties include repeated formal names and the source identity filter.

`SourceScopeQueries.lean` proves the complete mathematical query comparison.
`actual_related` compares the rebuilt actual assumption of each resolved
entry. `stack_actuals_related` retains every assumption in every scope.
`formula_related` compares the complete nested formula substitution fold.
`antecedent_related` combines both parts in the exact order used by the
source: actual assumptions remain ambient; the body passes through the scope
fold. No assumption states that the resulting query formulas are equivalent.
The proof derives their equivalence from source resolution and read equality.

`query_entails_iff` proves both directions of entailment for arbitrary finite
stacks and conflicting actual names. It constructs both environment maps
from the actual source fresh-name table. Its formula-name premise follows
from `observed_formula_names` for an observed refinement and from
`requirement_formula_names` for a literal guard requirement. The theorem uses
unrestricted environments. It does not claim sorted backend declaration
transport or exact agreement of an incomplete solver's Yes/Unknown verdicts.

This completes the mathematical formula query transport needed by Entails
and Satisfies under source-resolved nested substitutions. A caller must still
select the corresponding observed formulas, including negative Satisfies
requirements. `SourceHoldsQueries` now covers the generated contract names
and aliases. `SourceFullGuardBridge` and `FullGuardPruneStable` provide full
guard induction and candidate pruning composition under an explicit backend
name-transport stability contract.

Validation: `lake build MicroCFTA.SourceScopeQueries` succeeds with the pinned
Lean toolchain. The proof contains no admitted declarations or native proof
evaluation.
