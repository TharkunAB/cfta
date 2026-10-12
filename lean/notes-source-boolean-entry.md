# Independent Boolean operands in the public guard evaluator

`SourceBooleanEntry` records the public Boolean dispatcher before the later
substitution safeguards. `SourceSubstitutionPrecedence` is the current entry
and proves equality on complete terms and unambiguous sparse cells. It follows
`Refinement/Evaluate.hs` after the conjunction repair. `evaluate` dispatches
outer And, Or, and Not by polarity. It bypasses empty Substitute nodes. Each
other guard enters `evaluateScoped` once. A negative atom enters as Not atom.
The private helper allocates the actual table for that signed atom and then
runs the existing scoped worker from an empty substitution stack.

`scoped_eq` proves that signing does not change allocation and gives exactly
the worker's pushed polarity. Nonempty Substitute nodes remain opaque to the
entry dispatcher. The later safeguards can return Unknown at nested scope entry. In
particular, this repair does not assert distributivity through a nonempty
substitution or equate negative formula entailment with verdict negation.

`conjunction_yes` proves that the confirmed language of an outer conjunction
is the intersection of its component confirmed languages. The verdict fold
also handles Unknown. `normalize_evaluate` proves exact Yes, No, and Unknown
preservation when canonical conjunction normalization flattens, sorts, and
deduplicates outer conjuncts. This result needs no solver renaming contract.
It treats the solver as a stable pure callback; it does not compare IO traces.

`SourceBooleanBridge.unambiguous_subset` proves that the enclosing ambiguity
gate covers every scoped atom. `evaluate_refines` proves that sparse root
comparison can lose information but cannot change a decided complete result.
The proof includes Boolean branches with Unknown which do not determine the
final result. `evaluate_equal` transports each independently allocated atom
across equal planned reads. It reuses the complete scoped query proofs.
`complete_decision` connects a decided sparse cell to every complete term
with those reads. Conflicting actual names and fresh declarations are allowed.

`BooleanGuardPrune` retains the historical blanket gate. Its
variant query and fallback guard use `SourceBooleanEntry`. The global
always-unknown identity callback is an unconditional gate in that model.
Current source uses it only after an Unknown verdict. `CurrentGuardPrune`
models the current call order and proves exactness for unambiguous cells.
`prune_exact` proves confirmed-language preservation for every successful
candidate pass, including restoration of the original guard on ambiguity.
It composes the actual candidate loop and exact finite observation graph
specialization. The separate sparse graph and recursive adapters retain
their separately stated proof obligations.

`BooleanGuardCompile.decision` combines the current sparse entry and the
source compiler's error precedence. `classification` proves that diagnostic
probes cannot turn Unknown into a successful filter result. `decision_exact`
and `retain_iff` prove exact retention on unambiguous cells. That condition is
a proof premise, not a compiler precheck. Read agreement is explicit. This result does not assert that
the complete recipe compiler constructs its grouping keys correctly.

Grouping transport in both callers retains the explicit
`SourceQueryTransport.Stable` backend contract. Soundness alone does not imply
exact verdict stability under fresh-name transport. The supplied Z3 backend
has not been proved to meet that contract. Ambient declarations, assumptions,
name collisions, timeouts, and IO exceptions remain backend boundaries.

The old definitions stay available with a precise role.
`SourceGuards.evaluateWith` is the worker before both substitution safeguards.
`SourceGuards.evaluateGuardWithSame` is the historical public whole-guard
entry and the earlier private `evaluateScopedGuard` helper.
`SourceObservations.evaluateGuard` and `evaluateGuardWithShape` are wrappers
for that historical entry. `SourceFullGuardBridge`,
`GuardConjunctionNames`, `FullGuardPrune`, and `FullGuardPruneStable` prove
properties of that whole-guard allocation algorithm. Their scoped results
remain prerequisites of the current entry proofs. Their old public wrapper
names do not describe the repaired public Boolean dispatcher.

Validation: the pinned Lean toolchain builds `SourceBooleanEntry`,
`SourceBooleanBridge`, `BooleanGuardPrune`, and `BooleanGuardCompile`.
No theorem uses an admitted declaration or native proof evaluation.

`SourceConstraintConjunction.merge_exact` connects canonical guard merging to
independent complete evaluation. `edgeView_conjoin` combines that result with
the actual equality-class normalizer. This discharges the residual guard
conjunction premise of the constructor product used by enumeration.

At the earlier checkpoint, aggregate validation passed 310 jobs. The dependency audit checks 16,603
theorem declarations and permits only the standard Lean foundation axioms.
The existing Haskell suites pass 279 core, 193 generator, and 136 refinement
examples. The source reproduction is `repro/ConjoinScope.hs`.
