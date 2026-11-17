# Finite evaluator Type syntax

Status: **UNCOMPILED**. This is a conditional algebraic component. It is not actual source-role preservation and is not the full joint completion theorem.

The existing evaluator `EnumerationPendingAssignment.evaluateSlotsWith` is unchanged. The new `TypeFragment` predicate records exactly the supported Type layouts: marked holes, four rigid leaves, a catalog node with its declared arity and checked children, or the distinguished arrow with its fixed marker and two checked branches. The catalog may contain repeated or overlapping entries. No separation premise is needed.

`TypeFragment.fill_type` proves that filling the marked holes with finite Type terms preserves finite Type syntax. Its proof follows the grammar. The fixed arrow marker is not required to be an independently typed child.

`evaluateSlotsWith_type` proves finite Type syntax at every supplied evaluation fuel and marked raw variable. Fuel zero uses the typed default. A successor reads exactly `values[roots uv]`. An expanded slot uses the grammar and the strictly smaller fuel hypothesis for each marked hole. Missing, pending, and eliminated slots use the same supplied default.

The `expanded` premise is a property of the one fixed snapshot's stored syntax. It does not mention the future evaluator result. It uses the representative lookup that the existing evaluator actually reads. Therefore no separate root-role closure premise, UF path, Safe state, dependency levels, or stratification is needed for this finite typing result. Such facts remain necessary for separate stability, alias, and equation theorems.

The existing `SourceSynthesisProgramEnumerationRoles.FragmentRoles` deliberately leaves Type children unrestricted. It does not establish this Type layout property. The current `TypeIn` constructors concern completed terms, so they cannot directly represent holes. These are the reasons for the small new Prop grammar. There is no new runtime datatype, ledger, evaluator, or worker.

Actual source producers must still derive and preserve the marked role and the `expanded` syntax fact through real preparation, child calls, narrowing, and finalization on the same causal branch. The checked original-U leaf invocation supplies a real constructor base case. It does not discharge nonleaf or lazy Mu/Union history. The algebraic theorem must not be used as a new external source assumption or as proof of native/guard/historical compatibility.

The default may later be specialized to the literal `var1` leaf with `TypeIn.leaf`. No additional public specialization is needed here. The evaluator fuel is arbitrary; no original work, primitive, recursive, or evaluation fuel is increased.
