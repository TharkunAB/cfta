# Deletion predicates on live source support

The new `Compatible` predicate requires equal Boolean deletion tests on live fixed names and paired varying names. Its support is the existing `NativeNormalizationInputs.support`. It does not require agreement on unused captures or dead source rows.

`variable_input` restricts the predicate to the selected fixed value's free names or the selected varying label. `union_member` restricts it to each original member. `node_child` restricts it to a child of an original row whose symbolic children are all physically nonempty. That row test uses the original source input profiles. It is not a future assigned-output premise.

`extend` adds the local equality test to each predicate with Boolean OR. It takes the same live local-to-capture alias equivalence as the existing profile extension. The new local is always deleted on both sides. For a captured name, the parent compatibility equates the old cut and the alias condition equates its new local test. No injectivity or freshness of unused captures is assumed.

The extension accepts an explicit `smart : Bool`. Both binder forms have the same free-name support rule: remove the symbolic local from the body's support. An explicit rewrite of that existing rule transfers the old true-flag capture-support theorem to either flag. `local_cuts` derives the singleton local predicates by using false parent cuts. It needs only the same live alias condition.

Public argument orders are:

```text
Compatible expression inputs firstNames secondNames firstCuts secondCuts
variable_input index inputs firstNames secondNames firstCuts secondCuts compatible selected found
union_member members inputs firstNames secondNames firstCuts secondCuts compatible member present
node_child rows inputs firstNames secondNames firstCuts secondCuts compatible
  symbol guard children row live child present
extend smart body inputs firstNames secondNames firstCuts secondCuts compatible
  firstArgument secondArgument aliases
local_cuts smart body inputs firstNames secondNames firstArgument secondArgument aliases
```

The module has one public definition and five public theorems. It is a pure input restriction and extension result. It does not assume or prove equality of source outputs, a semantic payload law, a causal history, or general recursive source comparison. The existing profile compatibility, live aliases, and source self tests remain separate conditions.

Selected source SHA-256: `a3c80cce6ff2c3897f40c28e568caac48f42dca85153e2ca57897a5655c02c64`. Strict attempt 2 returned 0 with a literal 0-byte log. Canonical build 1 returned 0 and completed 599 jobs without warnings. Public probe 1 returned 0 and printed all six full declarations, proofs, and axiom reports with all eight required settings. Its 277366-byte log contains no printer omissions and uses only the standard allowed axioms. All selected executions used Lean 4.34.1, a five-minute cap, effective 4 GiB maximum and high memory limits, and zero swap.

Attempt 1 remains immutable. It failed because the general smart flag needed an explicit support-equation rewrite and `congrArg₂` was not available. Attempt 2 uses the support rewrite and core `congrArg`; it also adds the requested singleton-cut corollary. No hypothesis or conclusion of the original five heads was weakened. There are no new constructed pairs. Earlier sources and evidence remain unchanged. The component manifest uses an explicit file list and excludes shared mutable checkpoint files.
