# Current substitution policies and source correspondence

`FormulaTotalSubstitution` models the total public formula API from `092b56d`.
It retains unsupported function heads and substitutes their arguments.
`checked_agrees` proves agreement with successful checked substitution for all
syntax constructors. `checked_semantics` carries the existing simultaneous
semantics theorem to that domain. `guard_substitution` covers every name-only
substitution from guard evaluation. A checked nested argument failure takes
precedence over an unsupported outer head. A kernel-checked countermodel
shows why the total fallback has no general simultaneous function-value law.

`IntegerLabelTotalSubstitution` models current total label specialization.
It proves checked-success agreement and unconditional name/matcher laws.
The older checked specialization domain remains sufficient for the finite
settlement proofs. Those proofs do not yet cover every total fallback result.

`SourceEnclosingRenames` records the upstream `d6b8837` scope test. It rejects
an unknown actual identity whose ambient literal name is an enclosing formal.
It shares the complete syntax worker with the subsequent repair through an
explicit scope-check parameter. Its default retains the upstream policy for
regression proofs.

`SameScopeIdentityCapture` proves a defect that remained at `de910ea`.
A flat scope contains two replacements for formal `a`. The complete identity
quotient turns the first into `a->a`; identity removal then exposes `a->b`.
The sparse first entry remains a fresh variable. The source Z3 evaluator gave
complete No and sparse Yes. Pruning changed No to Yes. `validOutcomes` gave
`Right []`, while compilation produced one invalid tuple. The Lean witness
uses the already proved sound `NestedScopeCapture.solver`.

`SourceSubstitutionPrecedence` executes the repaired source list scan and
public evaluator. `precedence_false_iff` characterizes exactly the excluded
ordered pairs. `known_precedence` and `distinct_formals` prove the check is
inactive on those inputs. `complete_unchanged` proves complete evaluation is
unchanged for every term and every guard. `public_known` preserves every
verdict on unambiguous sparse cells. The nested and same-scope witnesses both
return Unknown in the repaired sparse evaluator; complete evaluation is No.

`BooleanGuardCompile` now classifies the repaired evaluator verdict directly.
Yes and No are the only successful classifications. Unknown remains an error.
`same_scope_compiler_unknown` checks the repaired witness. Its general
`decision_exact` theorem has an explicit unambiguous-cell premise. That
premise is not a source compiler precheck.

`CurrentGuardPrune` likewise evaluates first and uses the ambiguity flag only
on Unknown. It proves full finite candidate-loop exactness for unambiguous
specialization cells under the existing solver stability contract.
`same_scope_restores` derives restoration of the original full guard from the
concrete repaired Unknown verdict, including a previously retained prefix.
`BooleanGuardPrune` and `FullGuardPruneStable` retain the older blanket-gate
models. Their unconditional gate is not current source behavior.

## Remaining identity-quotient obligation

`SourceIdentityMap.names` already constructs the many-to-one sparse-to-complete
name map. `ActualQuotient` proves the actual identity classes. The remaining
proof must transport a complete query environment through every accepted
resolved scope under both runtime checks.

The existing `SourceResolvedTables.Aligned` relation requires unchanged
identity flags and mapped declarations. It cannot express an unknown sparse
identity becoming known or a fresh declaration disappearing. The existing
`SourceScopeEnvironment.environment_commutes` theorem requires injectivity.
The actual identity quotient need not be injective. A replacement relation
must preserve formal lookup after identity removal and track which fresh
actual values later scopes can read. Both runtime checks constrain exactly
these scope interactions, but the full derived forward-query lemma remains
open. Sorted declaration domains and positional Holds aliases must also be
included.

Once that forward query relation is derived, `SourceEntailment.identify_yes`
can transport logical positive entailment. It does not prove that the complete
solver returns Yes: a sound solver can still return Unknown. The existing
`SourceQueryTransport.Stable` contract covers two-way, lossless name transport.
It does not cover a many-to-one quotient. Exact confirmed-language preservation
on all accepted ambiguous cells therefore also needs an explicit one-way
backend verdict contract, or a stronger verified backend. No such property
is claimed for timeout-limited Z3 execution.

Validation uses the pinned Lean toolchain. The current Haskell suites retain
620 examples. Existing nested-scope repro files also cover the same-scope
case. The source repros now give `(No,Unknown)` and `(No,No)`, while both
compiler cases give `Right []` and `Left SolverUnknown`.
