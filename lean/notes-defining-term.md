# Parent guard measures and defining expressions

`DefiningTerm` follows `Expression.definingTerm` and the `termOf` helper in
`Compile.compileOpenNode.settle`. The source first tries `onlyPoint` for the
refined value. If that fails, the public extractor accepts one outer equality
with the value variable on either side. It prefers the left-variable case.
The repaired compiler callers then reject any extracted term that still
contains the refined value name. The public extractor does not search
conjunctions or perform an occurs check.

The precise guarantee is pointwise. `definingTerm_sound` proves that a
returned expression evaluates to the refined value in every environment
that satisfies the equality. It uses an explicit primitive equality law.
It does not claim that extraction alone gives a unique value.
`self_definition_not_unique` proves the boundary: `v == v` returns `v` and
holds both at zero and at one. This remains a permitted public extraction.
The compiler must not reuse that unresolved name as the parent value. A
public source probe confirmed that doing so can remove valid measured terms.
The caller gate now rejects that use.

`term_update_absent` proves independence when the returned expression does
not contain the refined value name. `definingTerm_unique` and
`definingTerm_exact` then give the unique value for each fixed ambient
environment. No independent solver verdict or satisfiability guess is used.

For the preferred singleton branch, `onlyPoint_table` reads the actual public
counter success from the returned value. `onlyPoint_ambient` uses the proved
parser name coverage to transport one-variable uniqueness into an arbitrary
ambient environment. `termOf_sound` combines the actual singleton branch and
the defining-equality fallback. `termOf_update` states the law for an explicit
refined value. `termOf_base` lets the parent evaluate the measure before that
value is assigned, provided the measure excludes the refined value name.
`independence_check` identifies the source free-name test with term-name
exclusion. `termOf_independent` derives that exclusion for every successful
current caller. `termOf_base_exact` applies it without an extra premise.
`onlyPoint_holds` also transports the singleton witness into any ambient
environment. `termOf_exact` proves refinement truth if and only if the
assigned value equals the returned expression. `termOf_exists_unique`
proves existence and uniqueness. These laws require no satisfiability
premise and thus exclude a vacuous implication for accepted measures.
The singleton branch uses the existing complete integer lattice semantics.
The generic equality theorem leaves all other primitive interpretations
explicit.

`single_assignment` proves that the source's identity-filtered one-entry
replacement has the exact environment-update meaning. `value_substitution`
uses the actual checked substitution traversal. `termOf_substitution_exact`
then discharges a parent Satisfies translation from the child's refinement
and its extracted independent measure. Checked substitution errors remain
explicit; they are not treated as false formulas or empty languages.

`definingTerm_substitute` proves exact syntactic transport of either equality
orientation when the refined variable is unchanged. `integerName_ne_value`
and `fill_keeps_value` derive that property for the actual integer filling
replacement list. `definingTerm_fill` proves that the source formula fill
returns a defining expression equal to the filled measure.
`filledTerm_semantics` gives its exact simultaneous assignment meaning.
There is no assumed term-codec inverse or solver alpha-stability condition.

Remaining caller obligations concern parent observation and formula
construction. Successful current `termOf` results exclude the refined name.
Raw public `definingTerm` results do not. The model does not turn either
extractor into a complete logical
solver and does not claim that every satisfiable refinement has a defining
expression.

Validation: `lake build MicroCFTA.DefiningTerm` passes with the pinned Lean
4.34.1 toolchain. No admitted declaration or native proof evaluation is used.
The initial extraction proof did not change Haskell. The later caller repair
adds the explicit self-dependency check in both source callers. Its source
regressions and full suite validation are recorded separately.
