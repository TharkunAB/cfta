# Concrete formula operations and entailment transport

`SourceFormula.lean` instantiates every `SourceGuards.Formulas` operation with
the repaired current Formula implementation. `checked_total` proves that a
name-only replacement list cannot fail. The proof covers every term and
formula constructor. It also proves that capture avoidance preserves the
name-only invariant below quantifiers. The executable total wrapper returns
the exact successful checked result. Its error arm is unreachable.

`FormulaExecutable.lean` supplies structural equality from the proved source
constructor comparison. It executes the complete source simplifier without
classical equality decisions. `simplify_eq` proves equality of its output
with `FormulaOrder.simplify`, which already has a full semantic proof. This
is output equality, not only equality of formula meaning.

The concrete guard backend includes repaired substitution, raw negation,
simplified conjunction, equality aliases, and free-name collection. The
free-name list abstracts HashSet iteration order. The source uses this list
as a set when it excludes fresh names. Both public guard wrappers now have
an executable instance for the full current formula syntax.

`scopes_semantics` proves the meaning of all nested simultaneous scopes.
The environment transformations run in the reverse order of formula
construction. `actual_assumptions_semantics` proves that actual refinements
retain their ambient meaning outside that scope fold. No assumption about
the whole guard evaluator occurs in these formula proofs.

`SourceEntailment.lean` proves the logical transport needed by actual-value
identification. `identify_yes` shows that unrestricted positive entailment
survives every simultaneous name identification. `rename_yes` includes the
explicit environment-domain condition needed by sorted solver declarations.
`rename_iff` identifies the additional obligation for refutations: every
original relevant environment must lift to a renamed admitted environment.
This obligation is only on the free names of the two query formulas.

The integer counterexample proves that this extra obligation is necessary.
`Top` does not entail `left = right`, but replacing both names with one
actual name makes the entailment true. This is the reason that an uncertain
actual identity cannot copy a negative solver answer. `decideWith_sound`
proves that the source No-to-Unknown safeguard preserves any sound per-query
solver result.

This closes the formula-interface gap in `notes-source-guards.md`. The full
sparse-to-complete guard theorem still needs a source table correspondence:
the allocated fresh names and representative paths must induce the proved
renaming and environment-domain maps. The theorem must also connect the
source symbol-sensitive observation signature to the complete term labels.
The current proofs do not assume either result. Concrete SMT translation,
sort inference, and solver correctness remain external contracts.

Validation: `lake build MicroCFTA.SourceEntailment` builds these three modules
with the pinned toolchain. There are no proof placeholders or new axioms.
