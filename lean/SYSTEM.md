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
and readback preserve that rank and every old closed language. Concrete
smart-constructor cleanup and runtime correspondence remain explicit.
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

`GeneratorCombinators` derives finite member counts, mixed-radix rank selection,
key partition coverage, conditioned join probabilities, and bucket mass
restoration. `groupOn` deliberately gives each member size one, as the source
documents. `RecipeCompile` models recipe routing, root/spine validation, error
precedence, integer-hole filling, closure, and observation metadata. Its
`atomic_pair_metadata_counterexample` derives the weight failure from those
source metadata branches. Heterogeneous Haskell callback and value records
still need their implementation correspondence.

[API-COVERAGE.md](API-COVERAGE.md) assigns every source module and exported
function family a semantic role. [COVERAGE.md](COVERAGE.md) records proof and
implementation correspondence obligations. A source port, a theorem about
that port, and a proved correspondence to Haskell execution are separate.

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
refinement suites pass in `nix-shell`: 273, 190, and 135 examples, respectively.
Existing property examples also run their configured generated cases.

An independent temporary source probe compared 5,000 finite grammars against
explicitly constructed term sets. Its cases combine overlapping binary
alternatives, empty child domains, child equality, and nested path equality.
It checked every decoded rank, both set equality and cardinality, inverse
ranking, and invalid ranks. All comparisons passed. The expected terms did
not use FTA enumeration or rank queries.

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

The Lean sources are handwritten models and ports. There is no verified
Haskell-to-Lean translation. Runtime containers, atomic cache operations,
Haskell laziness, machine conversions, external solver answers, random draws,
and user codecs have explicit contracts. Some internal driver invariants
remain proof obligations in the coverage ledger. Passing regression tests or
an axiom audit does not discharge those obligations.
