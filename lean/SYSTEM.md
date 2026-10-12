# Constrained languages, indexing, and distributions

## Specification

The source baseline is `origin/microcfta` at `d7f7c11`. This includes the merged
core-formula changes at `9ad319d`. The proof branch retains its earlier fixes.
It adds the integration repairs described below. Nothing is pushed.

A language is a set of finite ordered terms. A run is one derivation of a term.
Two runs can give the same term. A generator member is one source choice and
can share its term or decoded value with another member. These three objects
must not share a cardinality without an explicit equivalence proof.

The required laws are:

1. Grammar compilation preserves derivability in both directions. Each
   production consumes a constructor. Named references can form cycles.
   Equality constraints require existing equal subterms. Liquid constraints
   have an explicit interpretation and a supported decision procedure.
2. Enumeration contains all and only the accepted finite terms. A finite
   height or size bound restricts that statement to its stated bound. Increasing
   the bound must not remove a term. Every accepted finite term occurs at some
   bound. Recursion markers are not complete terms.
3. If the language has `n` distinct terms, decoding is a bijection from `Fin n`
   to that language. Both inverse laws hold. There are no unused valid ranks
   and no two ranks for one term. The empty language has zero ranks.
4. A requested relative weight `w(t)` gives probability `w(t) / sum w`.
   Weights are nonnegative and their total must be positive to define a
   probability distribution. The mathematical rank space does not depend on
   the weights. Source APIs can impose stricter input validation.
5. An exact optimization preserves accepted terms and their weights. It can
   change rank order if a rank translation preserves decoded terms. An
   optimization that retains representatives has a weaker contract and cannot
   be used to claim complete enumeration of the original language.
6. Efficient selection must use counts to skip whole blocks. A correct
   materialized reference index specifies the answer, but it is not evidence
   of an efficient implementation. Compilation cost and selection cost are
   separate.

## Checked composition

`Construction.Derives` defines the source grammar without an automaton.
`Construction.compile` constructs transitions and states without enumerating
terms. `compile_exact` proves both directions of the language correspondence.
`compiled_states_closed` proves finite state closure for finite named grammars.

`Language.mem_enumerate_iff` connects bounded reference enumeration to
independent finite-run acceptance. `LevelEnumeration.deeper_exact` proves the
source's first-deepest-child optimization. `stop_complete` proves that stopping
at a globally empty level cannot omit a later term. `BoundDepth.bound_exact`
proves the explicit graph depth rewrite, including the last-level leaf filter.

`DistinctRank` removes duplicate terms and proves both `Fin n` inverse laws.
`System.grammar_bijection` composes grammar compilation and complete finite
indexing. A finite cover supplies a height bound; it can contain extra terms.
The compiler still checks acceptance and retains exactly the declared terms.
For an infinite language, the theorem applies to finite bounds, not to a
nonexistent finite global cardinality.

`System.grammar_probability` gives the requested probability of each declared
term. A zero-weight valid term still has a rank, even though it has zero
sampling probability. Distinct values require a codec inverse law; an arbitrary
value map can merge the results of distinct term ranks. `optimization_correct` states the exact language/weight obligation and
proves cardinality and event-mass preservation once an optimization discharges
it. The component modules prove actual transformations; this composition
lemma is not evidence that every Haskell transformation discharges the
obligation.

`CoreFormula` and `CoreLattice` connect the integer formula fragment to the
checked signed indicator and polynomial eliminator. `LatticeSelect` connects
stored elimination levels and cumulative polynomials to natural section
counts, binary coordinate selection, and recursive ranking. `points_api_exact`
starts at successful public point construction and proves the full finite
bijection. `compiledPoints_exact` and `closePoints_exact` discharge the actual
point-decoder obligation for integer-leaf closure. The finite section
table is a proof witness. The decoder evaluates polynomials and does not build
that table.

`SearchCost.logarithmic_queries` proves that an interval with at most `2^k`
positions takes at most `k` cumulative-count queries. It does not treat
polynomial evaluation, arbitrary-precision arithmetic, or compilation as free
in a wall-clock complexity claim. `Decoder`, `PlanVariants`, `SizedRank`, and
`TablePosition` prove the corresponding finite plan and size indexing laws.

`Symbolic` proves overlap-safe union counting and local equality solver laws.
`SymbolicDriver` ports the mutual counting, normalization, selection, and inverse
ranking operations with both caches. Its complete examples exercise equality,
overlap, and rejection. `SymbolicNormalization` proves solution equivalence.
`SymbolicSelection` proves successful select/rank inversion with identical
cache flow. `SymbolicGraph` proves exact conditioning and projection coverage.
`SymbolicCounter.counter_correct_mutual` proves all six counter functions and
both caches. `SymbolicIndicators.counterMeaningFromRows` derives its semantic
interface from compiled guards and exact graph rows. `SymbolicCounterTotal` derives sufficient execution bounds and total stable
results for the complete counter. `SymbolicComplete.rows_full_index` now
derives total decoding and the complete distinct-term bijection with `Fin n`.
`SymbolicStructuralBudget.acyclic_full_index` derives language and budget laws
from copied operational rows and a topological rank. Pure interned allocation
and readback preserve that rank and every old closed language.
`SymbolicTotalAPI.allocated_total_api` includes smart-constructor cleanup,
normalized rows, hash joins, and total inverse ranking. Shared-cache worker
answers, stale-snapshot publication, and the public count-once callbacks have
separate proofs. `SourceSymbolicIndex` composes successful source constraint
compilation with these workers. `SourceSymbolicStableIndex` derives one fixed
index that all sufficiently complete executions share. Requested term weights
attach to that decoder order. Concrete runtime correspondence remains explicit.

`FiniteAutomatonDriver` proves the combined compact and symbolic cache
schedule. `SourceFiniteAutomaton` derives its guard, parser, normalization,
overlap, backend, and termination contracts from source graph rows. The
public result has exactly the distinct accepted terms and contiguous ranks.
An empty result is equivalent to an empty language on the supported input
domain. The remaining graph-readback and allocation requirements are
representation contracts, not an assumed root compiler correctness theorem.

`RecursiveUnambiguous` derives distinct size classes from the actual cyclic
overlap gate. `SourceCyclicAutomaton` preserves the public error order and
derives plainness, complete class counts, bounded distinct ranks, and the
bottom-up inverse. Cyclic imports reject constrained or ambiguous rows.
They provide exact finite size classes and bounds; an infinite language does
not acquire a finite global cardinality.

`Shrink` models every finite plan constructor and proves candidate validity,
strict rank decrease, non-growing size, and complete smaller-size traversal.
`TermRepresentation` proves the new small-arity representation round trips,
child lookup, and the required invariant for the raw `Many` constructor.

`Generic` implements finite datatype descriptor discovery, construction errors,
and codec rank laws. `Template.restrict_exact` proves exact restriction for all
five patterns, including cyclic graphs. `Binding` verifies the free-environment
cache key and closed-substitution shortcut. `EnumerationState` ports the
suspended-constraint caller and its recursion-marker behavior. `PruneSchedule`
ports pruning decisions, fallback, caching, and binder scheduling.
`EnumerationExact.runs_exact` proves actual initialized finite-term support
after returned residual checks. It constructs final rendering and stable
execution bounds from complete graph and exact-intersection contracts.
Source constructor, equality-product, and bounded-row adapters derive those
contracts. `EnumerationBuilderFastPaths` derives the finite memo traversal, both interning
caches, identity sorting/deduplication, terminal fast paths, and exact bounded
language. `EnumerationBinderExposure` proves closed self-unfolding
and exact successful rows. `LexicalBinderClosure` derives finite lexical
closure and terminating visited row exposure. `LexicalExposureLanguage`
proves that those rows have exactly the least binder language.
`LexicalBoundedBuilder` connects them to the memoized constructor builder.
Runtime binder identities, alpha-renaming, cleanup, and host storage remain
separate.
`InternedConstructorTemplates` and `InternedRecordCoherence` derive canonical
whole-record readback from empty-cache construction traces, including cached
free references and binder depth. `InternedStagedBinders` derives nested
dependency-first construction and a stable finite identity family after one
root build. General inner callbacks that depend on a fresh enclosing reference
still require a pending-cache-key argument.
`IntersectConstruction.constructed_intersection_total` proves that the complete
recursive intersection schedule terminates with exactly the common input
language. It starts from a finite payload completion trace, exact cached free variables,
canonical identities, and independent input semantics. Finite identities and
direct payload sizes follow from the trace. Closed-root reachability,
reset descent, and sufficient stable execution bounds are derived.
`MinimizeSchedule` implements the actual similarity/rewrite schedule. It
proves the historical accepted-root failure and the repaired root invariant.

Ordinary generator combinators retain members, including repeated values and
sometimes repeated constructor terms. Automaton imports instead count distinct
accepted terms. A claim of one rank per distinct term applies to the latter
API. It is not a property of arbitrary `elements`, maps, joins, and choices.
Similarly, LTA similarity minimization intentionally keeps representatives.
It cannot satisfy the requested exact-language optimization contract in
general, even after the root-deletion defect is repaired. The supplied paper's
Section 4.2 uses this weaker representative contract.

The pool wrapper also starts a new uniform distribution over retained entries.
It does not transfer discarded entries' mass to a representative. In the
checked three-entry example, the original similarity classes have masses
`2/3` and `1/3`; the minimized representatives have masses `1/2` and `1/2`.
`PoolMinimization` proves this behavior and its distinction from preserving
class probability. The public reproduction agrees with the model.
See [the pool distribution notes](notes-pool-minimization.md).

`GeneratorCombinators` derives finite member counts, mixed-radix rank selection,
key partition coverage, conditioned join probabilities, and bucket mass
restoration. `groupOn` deliberately gives each member size one, as the source
documents. `RecipeCompile` models recipe routing, root/spine validation, error
precedence, integer-hole filling, closure, and observation metadata. Its
`atomic_pair_metadata_counterexample` derives the weight failure from those
source metadata branches. Heterogeneous Haskell callback and value records
still need their implementation correspondence.

`OpenGroupedApplication`, `FinalObservationRanks`, and `FinalObservationMass`
derive finite applicative grouping, integer-point closure, parent settlement,
final observation regrouping, and nested frequency wrappers. They align each
member rank with its probability mass. Rank offsets use counts; branch
probabilities use the retained masses. Every query preimage is preserved,
including repeated values and repeated projected terms.

The finite size-field modules now derive the corresponding class positions,
member weight callbacks, sparse mass tables, and samplers. The proofs include
zero-size product splits, paid shifts, variable-width integer closure, and
final observation merging. The same-size atomic merge has its own probability
law. See [the size-field notes](notes-finite-size-fields.md).

`RecursiveTermAlignment` derives matching value and term index positions for
typed recursive products, choices, labels, and pays. It retains the private
recursion boundary and all duplicate member occurrences. The proof covers
complete bounded prefixes as well as each size class. General recursive
inverse callbacks and runtime knot construction remain separate. See
[the recursive alignment notes](notes-recursive-term-alignment.md).

`InternedFreshProbeKeys` derives pending-key separation when a normalized
inner probe retains the fresh outer reference. It also derives memo replay
when the outer variable was absent from the original free-variable set.
Normalization can erase an original dependency. That case still requires
an exact nested substitution identity proof. No closed-input collision was
established. See [the fresh-probe notes](notes-interned-fresh-probe-keys.md).

`SourcePlanPositions` and `SourcePlanPartition` prove both directions between
finite original ranks and size-class positions. All classes together form a
permutation of the complete rank interval. Their count sum equals the
original count. `PartialReductionCaller` proves exact inherited equality
descent and every completed repetition of the source reduction pass. It
also proves that larger execution bounds preserve completed results.
General reduction fixed-point termination remains open.

`GuardBuilders` and `ContractAssembly` derive standard argument arities,
consecutive paths, transition checks, conjunct selection, and capture-free
compact contract names. `DatatypeDecoder` proves that hashed constructor
lookup and full-term restoration equal direct lookup, even under hash
collisions. The constructor-probe models prove terminating witness and
context construction and coverage of every transition in an accepting run.
Finite probe success still cannot prove an arbitrary user codec total.

[API-COVERAGE.md](API-COVERAGE.md) assigns every source module and exported
function family a semantic role. [COVERAGE.md](COVERAGE.md) records proof and
implementation correspondence obligations. A source port, a theorem about
that port, and a proved correspondence to Haskell execution are separate.

The source query adapter now has an executable pure model in `SolverAdapter`.
It derives declaration coverage and the counterexample query, and it proves
sound returned verdicts from correct external solver answers. It retains
preflight Unknown, timed-out Unknown, rejected-query errors, and context
replacement as distinct cases. `RefinementValidation` proves finite located
traversal, base-symbol arity checks, and every signed guard-path endpoint.
Cycle detection and host IO remain explicit interfaces.

`DecoderDispatch` proves the actual cumulative offset builder and compiled
half-table dispatch. Zero-count branches remove no member. Every valid rank
has the same decoded member as concatenating the alternatives in order.
`DecoderDispatchCost` derives a lookup bound of `ceil(log2 k)` comparisons
for `k` positive branches. This excludes table construction, machine
arithmetic, and the selected branch's own decoding cost.

## Implementation comparisons and repairs

### Quantified substitution can change meaning

On `d7f7c11`, substituting an unused name can rename a quantified binder while
leaving the same name in an `App` function position unchanged. A nullary `App`
is translated as a variable by the solver. Thus this example uses an integer
binder, not higher-order quantification.

The original formula is `forall x:Int. x() = 0`. The replacement is
`unused := x`. Under an ambient assumption `x = 0`, the original formula gets
`No`, while the substituted formula gets `Yes`. Its free-name set changes from
empty to `{x}`. See [FormulaCapture.hs](repro/FormulaCapture.hs). The extended
syntax proof records the failing source operation separately from the
capture-avoiding substitution specification. The source now renames function
heads, substitutes nullary applications as values, and preserves repeated
binder shadowing. `substituteChecked` reports a non-name replacement for a
non-nullary function head, which the named-head syntax cannot represent.
The Z3 reproduction now requires the repaired `No` result.

### Observing an atomic pair changes bounded weights

An atomic choice has weights 9:1. Pair it with one leaf and add a constructor.
Both outcomes have size three. A tautological guard that observes the atomic
child preserves the unbounded PMF, but changes the PMF at bound three from
`9/10, 1/10` to `1/2, 1/2`.

`Compile.groupBuilt` omits retained class masses for atomic sources. A later
pair loses the atomic marker and falls back to counts. The current reproduction
is [CurrentFindings.hs](repro/CurrentFindings.hs). The existing
`RecipeCompile.atomic_pair_metadata_counterexample` proves the failure
through the actual singleton/pair/merge metadata rules.
`SizeMass.atomic_pair_count_fallback_changes_probability` also proves the
numerical difference independently. The repair retains `staticSampling` within-size weights for atomic members too.
`MassRetention.atomic_observed_pair_distribution` proves preservation for an
arbitrary positive atomic distribution and valid sibling.
`recursive_atomic_policy` proves agreement with the existing recursive rule.

### Minimization can remove the only accepted root term

The root accepts `b`. Another root transition reaches an accepted subtype
representative, but its own guard rejects. The schedule deletes `b` from the
root and only redirects incoming child references. The representative does
not become a root alternative. Structural productivity still holds, although
no root term is accepted.

The reproduction has a second variant whose rejecting guard remains unresolved
after pruning. Both `minimize` and `reduce` then change `[b]` to `[]`.
`MinimizeSchedule.full_schedule_loses_all_root_terms` proves the failure
through the complete executable schedule. The earlier
`Productivity.RootDeletion.root_deletion_counterexample` proves the denotation
difference independently. This violated even nonemptiness preservation. The repair installs the selected
root representative and checks its accepted derivation after every scheduled
rewrite has completed. `MinimizeSchedule.minimize_preserves_root_representative`
connects the complete repaired entrypoint to the original term or a surviving
accepted representative. Exact term equality remains a stronger contract.

### Union inside a nested binder can discard the enclosing reference

The baseline source documented this limitation. For `A = a | wrap(B)` and `B = A | b`,
`union` reads no alternatives from the open reference to `A`. The constructed
language becomes `{a, wrap(b)}` and omits `wrap(a)`.

[OpenUnion.hs](repro/OpenUnion.hs) reproduces the actual constructor behavior.
`OpenUnion.enclosing_reference_loses_term` proves the lost finite term. The repair retains open
operands in `InternedUnion` and resolves epsilon alternatives after binding.
`EpsilonUnion.collect_exact` proves that the terminating depth-first closure
retains all and only the accepted finite terms of its finite input graph.
The source tests include nested binders, epsilon cycles, conversion, and
intersection. See [notes-epsilon-union.md](notes-epsilon-union.md).

### Pruning an open nested binder can crash

The repaired union representation exposed a missing recursion-check case.
For `X = base | outer(a, Y)` and `Y = X | inner(a, Y)`, a guard on `outer`
reads `[1,0]`. The read reaches a fixed leaf. Validation returns `Right ()`
and recognition returns `Yes`. Before the repair, pruning instead raises
`nodeEdges: unresolved union reference` while inspecting the open binder.

The source now inspects an open binder's stored body before outer-edge
unfolding. It detects the enclosing reference and retains the guarded edge.
`PruneReads` proves the exact repaired gate and its structural termination.
The existing pruning suite checks the regression. The standalone
[PruneOpenBinder.hs](repro/PruneOpenBinder.hs) now validates, recognizes, and
retains the term after pruning. The full Nix suites pass 599 examples after
this repair. See [the repair notes](notes-prune-reads.md).

### Closing grouped applications can exclude every decoded term

Grouping an applicative pair can retain two private Apply edges in one support
node. Before the repair, `labelSupportWith` recognizes only a singleton Apply
edge. It wraps the multi-edge node. `labelTermWith` instead removes Apply from
each decoded term. For pairs over two indexed values, grouping by sum modulo
two and then adding a node label produces four decoded terms that the support
rejects. The support instead accepts four terms with an extra Apply node.
The inspection graph has the same mismatch.

The source now closes each retained alternative when a multi-edge node has
any closing private root. Ordinary roots keep the existing compact wrapper.
`SupportAlternatives.closeNode_exact` proves the full callback-image language;
its checked historical counterexample and repaired witness identify the lost
term. [GroupedSupport.hs](repro/GroupedSupport.hs) checks both public graphs.
All 600 existing examples pass: 274 core, 191 generator, and 135 refinement.
A separate source probe compares complete support and decoder term sets for
3,734 finite descriptions. All comparisons pass after the repair.

### Recursive term closing can cross an occurrence boundary

A direct recursive constructor exposes a second graph/callback mismatch.
For `recur (oneof [pure 0, node "s" self])`, the graph wraps its unresolved
reference as one child. The term callback instead removes private Choice
and Pure nodes from the selected recursive term. It produces a leaf `s`
where the graph requires a child. A recursive application spine can cause
the same disagreement after the language is bounded to a static source.

Single `recur` now inserts a private `Recursion` root inside its binder body.
Support, inspection, selected terms, and inverse ranking use the same root.
The wrapper survives size bounding. Engine terms change shape; user `surface`
terms, values, counts, masses, size classes, and rank order retain their
semantics in the original generator. Importing the raw support counts the new
Recursion roots as ordinary nodes, so its node-count bounds can increase.
Grouped recursion already has its AtKey/Family boundary.

`RecursiveSupportBoundary` proves the old rejection, exact wrapper inverse,
parent/spine behavior, unchanged projection and member distribution, and
acceptance of the complete repaired example stream. The source reproduction
[RecursiveSupport.hs](repro/RecursiveSupport.hs) checks ten variants, their
support and inspection membership, inverse ranks, PMF, and user surface.
All 601 existing examples pass: 274 core, 192 generator, and 135 refinement.
A separate sweep checks support membership of every bounded decoded term
for 540 recursive descriptions. See [the proof notes](notes-recursive-support.md).

### Grouped function spines can retain removed private roots

The sixth repair closes a grouped root directly. A later application can
also use that group as its function child. The old helper then treats the
whole group as one argument. The term callback flattens the selected Apply
spine. Both decoded terms of a two-element example remain outside the graph.

The support helper now returns one ordered child sequence per alternative.
It appends the new argument to each sequence and emits one labelled edge for
each result. `SupportSpineAlternatives.close_exact` proves exact agreement
with the callback. Checked examples prove the old loss, the repaired witness,
and rejection of crossed pairs. [GroupedSpine.hs](repro/GroupedSpine.hs)
checks seven public variants, including correlated and nested grouped spines,
exact support and inspection languages, and inverse ranks.
All 602 existing examples pass: 274 core, 193 generator, and 135 refinement.
See [the proof notes](notes-support-spine-alternatives.md).

### Sparse nested substitution can admit an invalid term

Two equal inner actuals named `a` have refinement `value = 0`. An outer scope
substitutes `b` for formal `a`. An inner scope substitutes the actuals for
`x` and `y`, then requires `x = 0`. Sparse evaluation allocates two fresh
names and returns Yes. Complete evaluation merges the actuals, applies both
scopes, and requires `b = 0` from the ambient assumption `a = 0`. It returns No.

Pruning previously discharged that guard and admitted the rejected term.
The generator compiler had the same defect: `validOutcomes` returns no values,
while compilation produced one invalid tuple. Pruning now retains the original
guard before an ambiguous sparse query. Compilation reports `SolverUnknown`.
This error does not mean an empty language. A valid ambiguous group can require
more precise identity splitting or complete-member checking before compilation.

`NestedScopeCapture` proves the original sparse Yes and complete No with a
proved sound integer callback. `PruneAmbiguity` proves restoration for every
successful ambiguous candidate pass. The full and memoized candidate models
include the gate. The compiler model checks its error precedence.
See [the proof and repair notes](notes-nested-scope-capture.md),
[NestedScopeCapture.hs](repro/NestedScopeCapture.hs), and
[NestedCompileCapture.hs](repro/NestedCompileCapture.hs).

### Equality reduction can grow equivalent guards without stopping

An acyclic three-leaf equality class uses three different residual guards
which all accept the same leaf. The old conjunction constructor retained
nested duplicate syntax. Repeated narrowing increased each guard from size
9 to 29 to 89 and kept allocating new identities. The public pruning call
did not finish. `PruneTerminationGrowth` proves growth for every operand order.

Conjunction now flattens outer And nodes, removes Top, and sorts and removes
duplicate conjuncts. It preserves scopes, negation, and disjunction as atoms.
`GuardConjunction` proves normalization, absorption, and bounded atom counts.
`GuardConjunctionNames` proves exact public evaluation and fresh-table equality.
The source example stabilizes at size 5. A nested correlation regression
checks that the repair does not add crossed children. All 606 existing suite
examples pass: 277 core, 193 generator, and 136 refinement.
This does not establish general recursive pruning termination.
See [the proof notes](notes-prune-conjunction.md) and
[PruneConjunction.hs](repro/PruneConjunction.hs).

### Combined guards can change an operand's meaning

A separate confirmed example has input guard results Yes and No, but the
combined And guard returns Yes. Actual-name allocation originally examined
the entire combined guard. A conflict introduced by one operand allocated a
fresh name in the other operand and changed its nested substitution behavior.
Actual FTA intersection then admits a term rejected by one input. Both inputs
and the result validate. This is distinct from sparse-observation uncertainty.
The public entry now allocates each outer Boolean operand independently. It
keeps nonempty substitution scopes intact and makes empty substitution an
identity. Negative atoms retain formula refutation, including missing paths.
The retained [source reproduction](repro/ConjoinScope.hs) now returns input
and intersection membership `[Yes, No, No]`. All 608 suite examples pass.

`SourceBooleanEntry.conjunction_yes` proves independent conjunction semantics.
`normalize_evaluate` proves canonical conjunction preserves all three verdicts.
`SourceBooleanBridge`, `BooleanGuardPrune`, and `BooleanGuardCompile` prove
successful current sparse decisions under the explicit backend transport
contract. `SourceConstraintConjunction.edgeView_conjoin` supplies the actual
residual guard law to constructor intersection. See the
[public-entry notes](notes-source-boolean-entry.md).
The original whole-guard entry remains a model of the current private scoped
helper. Its historical public wrapper names do not describe the repaired
public dispatcher.

### Recursive equality reduction expands equivalent domains

Let `A = mu x. (a | f x | x)` and `B = mu x. (a | f x)`. Both accept
`f* a`. A triple with children `[A,B,A]`, constrained equal, caused one public
`reducePartially` call to exceed the retained three-second limit. Completed
internal passes increased binder depths from `[1,1,1]` to `[3,2,3]`,
`[6,4,6]`, and `[14,9,14]`. This is confirmed representation growth;
unbounded nontermination was not proved. The example is a closed equality
FTA. The LTA validator rejects its cyclic equality targets.

The source now skips narrowing a class when any path crosses recursion or
its endpoint contains recursion. It retains the original equality constraint.
The repaired [reproduction](repro/RecursiveReduction.hs) completes and checks
accepted equal triples, rejected unequal triples, and bounded enumeration.
An existing structural test now expects recursive children to stay folded.
Acyclic sibling domains still narrow. All 610 suite examples pass.

`RecursiveReductionBarrier` proves exact gate selection, bounded path descent,
unchanged constrained language for completed reduction, and immediate
stability when all classes are blocked. `RecursiveReductionSourceOrder`
proves that the former finite three-leaf guard-growth family reaches a
structural fixed point within two passes. Its comparator laws are derived
from the actual source guard and formula order. General finite-DAG reduction
termination remains open. See the [source findings](notes-recursive-reduction-growth.md),
[barrier proofs](notes-recursive-reduction-barrier.md), and
[structural order proofs](notes-structural-order.md).

### Observed imports can drop every explicit-union term

The closed automaton `mu r. (r | a)` accepts exactly `a`. Its union with
`b` accepts `a` and `b`. Both validate and import correctly by themselves.
When an always-accepting parent guard requests an observation, the old
`splitByObservations` unfolds the binder into an explicit union and falls
through to an empty result. Compilation then reports `EmptyGenerator`.

The source now exposes an `InternedUnion` with the existing finite
`nodeEdges` epsilon closure and uses the ordinary constructor split.
Both whole-root and nested requested observations preserve the imports.
The existing suite regression and [ImportUnion.hs](repro/ImportUnion.hs)
retain the examples. The repair passed all 611 suite examples.
`ImportObservations` derives exact requested paths, child-map readback,
observation keys, complete partition coverage, and disjoint group languages.
It composes the local distinct decoders. Binder and epsilon row exposure
remain explicit interfaces to the existing graph proofs.

### Observed recursive imports lose their size indexes

A separate productive-recursion import reaches `filterGroupsM` with a valid
finite map of recursive observation groups. That function's finite-only
accessor rejected it as `UnboundedGenerator`. The source now filters the
ascending key map directly. It retains each complete recursive record and
its original tied program. Internal calls can still reach a key that the
filter removes from the public map.

`RecursiveGroupFilter` proves exact retained keys, ascending order,
at-most-once callbacks, first-error behavior, and complete-record equality.
Counts, decoders, samplers, masses, and metadata remain unchanged within
each retained group. This does not assert unchanged probabilities after
selection normalizes the retained groups. Existing regressions and
[RecursiveGroupFilter.hs](repro/RecursiveGroupFilter.hs) check size classes,
bounded values, and inverse ranks. All 613 suite examples pass.

### Bounded construction loops on retained empty binder cycles

`createMuDontCleanup id` and a retained nested forwarding binder are closed
public inputs with empty least languages. Their `nodeEdges` calls returned
empty immediately. The old `boundDepth 0` calls exceeded a one-second limit.
The separate root-Mu branch unfolded at the same depth before memoization.

The source now exposes every interned root through `nodeEdges`. Its visited
closure resolves epsilon cycles before bounded recursion visits constructor
children. The repair preserves the depth consumed by each constructor.
`LexicalBinderClosure` derives a finite request inventory from closed syntax
and proves exact visited row exposure. Runtime binder interning and
alpha-renaming remain explicit representation interfaces.

The existing regression and [BoundRetainedBinders.hs](repro/BoundRetainedBinders.hs)
check the empty cases and a productive nested recursive grammar. Depths zero
through three give 1, 3, 7, and 15 distinct terms. Every decoded rank has its
inverse. All 614 suite examples pass. See [the closure notes](notes-lexical-binder-closure.md).

### Self-dependent measures can lose valid expressions

A leaf with refinement `v == v` does not define one integer. The public
`definingTerm` extractor nevertheless returns `v`, as its syntax contract
permits. Two generator callers treated that result as an exact measure.
Pairing this leaf with a symbolic integer `x` and adding the measures
produced `v == v + x`. A parent guard could then disagree with complete-term
validation: the complete path retained `(0,1)`, while symbolic compilation
returned an empty generator. No reserved name was supplied by the caller.

Both callers now reject fallback terms that mention the refined value.
The singleton `onlyPoint` branch retains priority. A used inexact child
measure reports `InexactMeasure`; unavailable parent extraction reports
`IntegerLeafRead`. The public syntactic extractor is unchanged.
`DefiningTerm.termOf_exact` derives existence and uniqueness for every
accepted extraction. `ParentGuardFormula` uses that result to derive the
parent formula without assuming target satisfiability.
[SelfDependentMeasure.hs](repro/SelfDependentMeasure.hs) checks both parent
guard forms, listed and symbolic children, independent measures, and the
singleton-first case. See [the finding](notes-self-dependent-measure.md).

### Recursive open group positioning can throw a partial-map exception

Put a choice between a productive recursive import and bounded symbolic
integers below a constructor. Both `uniformly` and `oneof` raised `Map.!`
during compilation. `repositionOpen` built its position table through
`cardinalities`, which cannot return counts for recursive groups. It
replaced that error with an empty key list, then indexed the empty table.

`repositionOpen` and the analogous `joinPositioned` now use `groupKeys`.
The keys remain available when the language has no finite cardinality.
The open closure still reports its existing `UnboundedGenerator` result.
This repair does not add recursive symbolic integer closure.
`GroupPositions.regroup_lookup` derives a valid lookup for every retained
key. The map fold preserves first positions and duplicate identities.
[RecursiveOpenPositions.hs](repro/RecursiveOpenPositions.hs) checks the
public error path. See [the position notes](notes-group-positions.md).

## Rebase integration repairs

The previous weight repair introduced `keyedBucketMasses`. New upstream
constructors pay one unit of size. Both `Types.payGroupsWith` and the open
compiler's `labelBucket` must shift those masses when they shift members.
Without the shift, retained regressions reverse relative weights or raise
`Ratio has zero denominator`. Both paths now move the masses with their
members. Atomic reconstruction also retains the original size under pays.
`SizeTransport.pay_coherent` and `pay_class_probability` prove the required
transport law, and `stale_mass_counterexample` proves why the old keys fail.

The retained regression fixtures and reproductions now use the current
constructor sizes, `Term` representation, and sorted core-formula declarations.
No new package test suite was added. The existing core, generator, and
refinement suites pass in `nix-shell`: 282, 194, and 142 examples, respectively.
This includes the later measure and recursive-positioning regressions.
Existing property examples also run their configured generated cases.

An independent temporary source probe compared 5,000 finite grammars against
explicitly constructed term sets. Its cases combine overlapping binary
alternatives, empty child domains, child equality, and nested path equality.
It checked every decoded rank, both set equality and cardinality, inverse
ranking, and invalid ranks. All comparisons passed. The expected terms did
not use FTA enumeration or rank queries.

Further support checks cover 1,536 mixed grouping and recursion descriptions
and nine automaton-import variants. All pass, with no skipped cases. A
separate probe checks 144 weighted compilation descriptions across nine size
bounds. It compares values, member sizes, bounded PMFs, and exact sampler
masses through atomic, paid, and keyed products. All pass. Recursive
intersection matches independently intersected term sets for 2,080 grammar
pairs through depth four. These finite comparisons do not establish universal
source correctness.

A separate source probe built a shared depth-60 binary chain under an equality
between two children. The FTA describes `2^60` distinct terms. Exact counting
and four distant decode/rank round trips passed without language enumeration.
The same check passed at `2^80`, beyond 64-bit machine cardinality.
The measured CPU times were about 1.4 ms and 9.4 ms for the evaluated operations
in these local runs, excluding process startup. This is a feasibility check, not a
benchmark or a general complexity bound. The temporary probes are
`/tmp/microcfta-distinct-conformance.hs`, `/tmp/microcfta-large-index.hs`, and
`/tmp/microcfta-large-index-80.hs`.

## Explicit limits

General quantified or nonlinear integer constraints do not have a complete
terminating solver contract. The lattice backend rejects unsupported syntax,
including every `Ite`, even when a particular input denotes a finite set.
Solver `Unknown`, timeout, unsupported syntax, unbounded cardinality, and
invalid callback results are errors or explicit unresolved states. They are
not proofs that the mathematical language is empty.

The finite reference index materializes terms. It is used to specify the
bijection. The source symbolic counter and rank decoder have separate models
and proofs. Observing an already-built finite source still enumerates every
member in `groupBuilt`; a fast rank decoder does not remove that compilation
cost.

Soundness of an incomplete solver does not ensure identical Yes/Unknown
results after fresh variables are renamed. `GuardAlphaBoundary` proves this
with equal source signatures and a sound name-sensitive callback. The current
Haskell evaluator reproduces `(Yes,Unknown)`. Both logical requirements are
valid. Exact operational verdict preservation requires an additional
renaming-stability contract. The supplied Z3 adapter also reproduces
`(Unknown,Yes)` when an unused ambient declaration collides with a generated
actual name. It rejects that declaration before asking Z3. This loses a
confirmed result without admitting an invalid term. The allocator does not
see the complete ambient declaration set. See [the checked boundary](notes-guard-alpha-boundary.md).

The Lean sources are handwritten models and ports. There is no verified
Haskell-to-Lean translation. Runtime containers, atomic cache operations,
Haskell laziness, machine conversions, external solver answers, random draws,
and user codecs have explicit contracts. Some internal driver invariants
remain proof obligations in the coverage ledger. Passing regression tests or
an axiom audit does not discharge those obligations.

The actual identity supply stores signed machine words. Its identities are
distinct within one full word period, including its negative half. A full
wrap repeats the initial identity. `InternedIdentityWords` proves both
facts. Global freshness therefore requires a bounded allocation lifetime
and linearizable atomic draws. This is a representation boundary, not a
reproduced practical failure. See [the identity notes](notes-interned-identity-words.md).
