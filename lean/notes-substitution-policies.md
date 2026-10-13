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

The current scan matches upstream `c4b4f97`, included in `4897831`. It rejects
a later replacement only when that replacement is not a literal identity.
`identity_only` and `append_identity` prove that repeated literal identities
do not introduce an ambiguity rejection. The former local scan rejected
these safe cases too. The existing upstream guard test confirms sparse and
complete Yes for `a->a, y->a, a->a` with equal compound actuals.

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

## Derived logical identity-quotient transport

`SourceQuotientEnvironment` gives a noninjective scope relation. It preserves
first-nonidentity lookup. It uses both executed scope checks to control new
identity entries and enclosing renames. `SourceIdentityQuotient` derives that
relation from actual sparse and complete allocation tables. It permits an
unknown identity to become known and a fresh declaration to disappear.

The refined scan needs the allocator's original-name coherence. If one
actual keeps its original name, every actual with that name keeps it.
`SourceIdentityQuotient.logical_coherent` derives this property from the
conflict table. `resolved_coherent` and `SourceQuotientQueries.stack_coherent`
carry it to every executed scope. After an earlier replacement becomes an
identity, later replacements at the same formal are therefore also identities.
`scope_environment` uses this fact to preserve first-nonidentity lookup.
The source query and pruning theorems derive this invariant internally.
They do not require a new client contract.

`SourceQuotientQueries.entails_yes` transports positive entailment through
accepted resolved scope stacks. It includes all actual assumptions and both
ambient and generated sort domains. `entails_yes_unrestricted` composes
`SourceEntailment.identify_yes` directly. `SourceQuotientHolds` adds positional
declarations, refinement assumptions, and aliases for repeated target paths.
These proofs require no injectivity premise and no unambiguous-table premise.

`SourceKnownIdentityMap` constructs a reverse map for the active known actuals.
`SourceKnownQueryTransport.solver_no_logical` extracts known identity flags
from the source No gate and proves negative Entails transport. It does not
assume a general reverse quotient theorem. `SourceQuotientGuards.worker_yes`
and `public_yes` compose these results through every guard constructor and
either polarity. Negative Entails refutes entailment. Negative Satisfies and
Holds entail the negated formula, as the source does.

`SourceQuotientExample` is an accepted ambiguous guard. Its sparse evaluator
returns Yes. Its complete evaluator returns Unknown with the same proved
sound callback. `logical_complete` and `guard_logical` prove its complete
query and guard judgments. Thus solver soundness does not imply exact complete
backend Yes preservation. This is a backend-contract counterexample, not a
new Haskell defect.

`SourceCurrentReadTransport` and `SourceCurrentReadBridge` extend the existing
lossless table-name correspondence to ambiguous tables and the repaired
worker. They derive equality of identity flags and both runtime checks.
`CurrentGuardLogicalPrune.prune_sound` proves that every returned term belongs
to the original automaton and satisfies the complete logical guard. The
source still evaluates each candidate before checking ambiguity on Unknown.
`SourceCompleteLogical` handles the original guarded edge on fallback.
`compile_retained` gives logical safety for successful compiler retention.

The exact-term sparse-to-complete logical theorem requires only the stated
formula interpretation laws and solver soundness. The finite planned-read
adapter also uses `SourceQueryTransport.Stable` for lossless fresh spelling
changes: refinement-only placeholder names can change the avoid list.
This contract is separate from many-to-one actual identification. No exact
verdict stability under that quotient is assumed or proved. Exact confirmed
backend-language preservation on all accepted ambiguous cells still requires
a suitable backend contract. No such contract is established for timeout-
limited Z3 execution. The logical pruning theorem is one-way safety, not
logical completeness or equality with complete backend-confirmed membership.

Validation uses the pinned Lean toolchain. The current Haskell suites retain
620 examples. Existing nested-scope repro files also cover the same-scope
case. The source repros now give `(No,Unknown)` and `(No,No)`, while both
compiler cases give `Right []` and `Left SolverUnknown`.
