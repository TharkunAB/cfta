# Full formalization coverage

## Objective and completion rule

Formalize the complete microcfta design in Lean. Prove that generation covers
all required terms, that sampling has the specified probabilities, and that
each optimization preserves its stated semantics. Keep the correspondence to
the actual Haskell algorithms explicit. Record implementation errors while
continuing the other proof work. Report the findings at the end.

This ledger distinguishes system modeling from complete implementation
verification. Every source module has an explicit semantic role and boundary.
Passing builds, theorem counts, and finite examples do not verify the whole
implementation. A proof row is complete only when its executable algorithm
has a checked semantic theorem and its implementation correspondence is
established. A theorem whose main algorithmic obligation is a premise
does not close that obligation. An implementation counterexample prevents a
soundness claim for that path; it does not remove that path from the scope.

Source baseline: `origin/microcfta` at `8ac24bb`. This includes the merged
core-formula changes at `9ad319d`. The current semantic specification and
implementation findings are in [SYSTEM.md](SYSTEM.md). All 66 source modules
are inventoried in [API-COVERAGE.md](API-COVERAGE.md).

Current update: PR #97 adds merged peer projections to equality narrowing.
The new `MergedProjectionBound` covers the complete physical projected-leaf
schedule with that operation. The previous worker retains its separate proof. Full nested
free-name interpretation and the global decoded free-name heap are now
proved, including historical literal-probe boundary exclusion. General
Mu-boundary replay and first-run no-pending remain open. See root
[FINDINGS.md](../FINDINGS.md) for current status and validation.

The latest physical equality work derives admitted leaf readback, identity,
intersection, and projection union. A normalization phase handles arbitrary
initial outer guard syntax. Physical raw construction preserves rejected
sentinel requests and derives whole-node identity from the accepted row set.
Physical Cartesian intersection derives exact raw readback and strict rank
decrease. Its generated finite carrier preserves initial raw guard syntax.
Finite occurrence compilation and recursive workers derive complete payload
availability and readback. Ordinary occurrence trees now have exact complete
recursive required-path correspondence. Physical leaf
intersection and projection union have finite-cache record correspondence;
physical path projection derives completion and available payloads. Endpoint
projection, simultaneous edit, and schedule composition remain open.
Full nested construction derives pending-reservation origins, complete old probe footprints, pending
preservation, and earlier readback of old identities. The remaining general
completion step is general absent-reference replay; recursive erased-edge
construction already completes at arbitrary depth. Structural erasure and
mixed retained/erased source contexts also derive first completion.
The unfolding rank depends only on reachable shallow values.
Unrelated deep cache records are allowed;
arbitrary nested Mu bodies remain open. Separate actual completion and strict
decrease results allow arbitrary-depth closed Mu children in ordinary bodies.
Source marker provenance also admits open nested records for one-step
completion and decrease. General repeated unfolding remains unresolved.

The upstream base includes the seventeen earlier repairs. This continuation
also repairs same-scope identity-replacement precedence and recursive
construction payload queries. Formula substitution
preserves bound application names. Observed atomic members retain their
within-size weights. Minimization installs and checks accepted root
representatives. Open unions retain epsilon operands. Pruning inspects stored open binder bodies before following recursive reads.
Grouped private alternatives now close in agreement with decoder terms.
Recursive members retain one private boundary in every structural record.
Grouped function spines retain each alternative's correlated children.
The evaluator rejects uncertain enclosing renames and identity-precedence
changes before sparse substitution can discharge their guards.
Canonical conjunctions stop the reproduced acyclic equality-reduction loop.
The public Boolean guard entry now allocates each outer operand independently.
Recursive equality classes remain enforced when the current constrained-recursion gate skips narrowing.
Observed imports now expose explicit union alternatives instead of dropping them.
Recursive observation groups retain their size indexes during key filtering.
Bounded construction now exposes retained binder cycles with the visited closure.
Measure callers now reject self-dependent extracted values.
Open group positioning now reads recursive keys without a cardinality query.
Unfinished recursive occurrences keep independent construction tokens.
Payload queries reject them consistently across rebuilding phases. Nested
completion preserves enclosing tokens and removes the completed token.
Grouped recursion validates the discovered table against its final probe.
Typed constructor programs pass this check with their previous exact minima.
Existing suites pass 284 core, 194 generator, and 142 refinement examples on `de910ea`. Historical
counterexamples remain checked against their explicitly named baseline
models. The positive repair theorems are separate.

## Coverage ledger

| Area and source modules | Checked foundation | Source correspondence and remaining work |
| --- | --- | --- |
| Term/path semantics: `Path`, `Term`, `Internal.Tree`, `Generic`, `Simple` | `Language`: finite runs, bounded enumeration, path lookup, equality sharing. `TermRepresentation`: all small-arity constructors, invariant, round trips and lookup. `TermOperations` and `ChildBuilder`: complete indexed construction, edits, preorder traversal and arbitrary folds. `LevelEnumeration`: first-deepest split, exact next level and safe empty-level stopping. `BoundDepth`: exact graph rewrite. `Construction`: nested constrained grammar compilation and finite state closure. `Generic`: terminating finite descriptor discovery, exact language, growth/domain failures and codec rank laws. `Template`: all five patterns and exact graph restriction. | Concrete sequence/hash storage, GHC generic type metadata, binder conversion and public wrapper correspondence. `FTAValidation`, `FromTerms`, `GraphTrim` and `StateMap` now verify the explicit graph operations. |
| Constraints: `Constraint`, `Equality.Constraint`, `Refinement.Guard` | `Guards`: Boolean evaluation and splitting. Concrete trie construction, ordered paths, prefix checks and descent. Canonical connected components and congruence saturation. Unconditional termination, exact semantics, constructive finite models, and rejection iff no model exists. | `SourceGuardSplit` proves the current semantic/residual split for every constructor and all three verdicts. `ConstraintIndicators` proves the whole supported signed compiler. `SourceEqualityGuards` derives its exact indicator from the current complete evaluator, including missing equality paths. `SourceIndicatorCompiler` connects every successful full-Guard compilation to that law and preserves exact unsupported errors. `ArrayUnionFind`, `EqualityArray` and `ArrayBounds` now prove concrete array workers, complete class iteration/readback/grouping, connected components, finite execution and index bounds. `EqualityIndex`, `EqualityPartition` and `EqualitySource` close path allocation, canonical readback and repeated array normalization. Physical storage, residual guard decisions and public arity wrappers remain. `EnumerationState` models suspended-path scheduling separately. |
| Interning and recursion: `Interned.Type`, `Interned.Operations`, `Interned.Cache`, `Interned.Memo`, `Interned` | Synchronous graph intersection in `Language`. `Cache`: fresh identities, first-writer insertion, finite interleavings, memo results, sharding with collisions. `Binding`: free-variable dependency, restricted environment cache keys, identity substitution and depth-probe distinction. `BoundDepth`: exact graph copy. `OpenUnion`: historical loss and repaired witness. `EpsilonUnion`: terminating depth-first closure and exact epsilon elimination. | `InternedIdentityWords` derives finite-word freshness within one allocation period and proves wraparound repetition. Runtime map/atomic/type-cast correspondence, fresh binder alpha-renaming, the SCC/lazy-map conversion adapter and lexical-to-runtime identity correspondence. `IntersectConstruction.constructed_intersection_total` derives termination and exact language from a finite payload-completion trace, cached free-variable equations, canonical identities, and exact closed copying. Sizes, finite identity sets, reference coverage, and closed reachability are derived. `IntersectInput.finite_intersection_exact` proves every successful recursive intersection against independent finite input derivations. `IntersectDomain` proves lookup coverage, and `IntersectProgress` proves local progress between resets. `BinderCycles.cycles_closed_total` proves total exact cyclic graph-to-binder construction from complete cycle marking; `BinderComponents` proves component sharing. `RedundantEdges` and `GraphRewrite` prove complete row reduction and cyclic graph preservation. `BinderLanguage` proves least-language unfolding and both cleanup cases. `EnumerationBinderExposure` proves closed self-unfolding, exact successful exposed rows, and that raw Rec is unreachable from a closed input. `LexicalBinderClosure` derives finite lexical closure and visited row exposure. `InternedBinderRebuild` derives the prepared binder substitution, fresh alpha replacement, cleanup, and closed exposure from syntax. `InternedSubstitution` derives the full nested worker, fresh allocation trace, exact open-environment language and closed unfolding. `InternedBinderProtocol` derives the source two-probe key, exact replay after cache growth, and restricted binder memo readback. `InternedConstructorTemplates` derives ordinary/union requests, cached metadata, enclosing Mu completion, and whole-record identity replay. `InternedRecordCoherence` derives global key/record coherence, complete readback and finite record inventory from empty construction traces. `InternedStagedBinders` derives nested dependency-first construction and the stable finite identity family after one root build. `InternedFreshProbeKeys` derives fresh-reference key separation and originally irrelevant-variable memo replay. Dependency erasure during normalization, full fresh-outer-dependent nested completion, and stable lexical-to-runtime identity readback remain. |
| Enumeration: `Enumeration`, `Internal.UnionFind`, `Equality.Operations` | `Language`: reference enumeration and sharing. `UnionFind`: exact terminating state operations. `Fragments`: hole resolution, slot intersection, assimilation, and combined union/assimilation assignment semantics. `EnumerationState`: complete fuelled caller, suspended paths, expansion ordering, ancestry cutoff, witness accumulation and rendering, with source behavior examples. | `EnumerationCorrectness` derives storage, allocation, union/assimilation semantics and concrete renderer soundness. `EnumerationSchedule` and `EnumerationDriver` prove the entire caller storage/live-root/alias invariant and completion state. `EnumerationSoundness` proves complete caller assignment simulation and acceptance. `EnumerationProgress` derives no-stuck expansion under a satisfying assignment. `EnumerationAssignment.runs_sound` constructs final assignments and proves actual-run acceptance under returned residual checks. `EnumerationExact.runs_exact` proves actual initialized finite-term support in both directions, including final rendering and sufficient stable execution bounds. `EnumerationConstructors`, `EnumerationIntersection`, and `EnumerationEquality` derive complete graph and intersection invariants from source rows and equality normalization. `EnumerationBoundedRows` proves exact depth copying. `EnumerationBuilderFastPaths` derives exact finite memo traversal, two-stage edge/node interning, sorted/deduplicated identity readback, terminal fast paths, and bounded language. `EnumerationBinderExposure` derives closed self-unfolding and exact successful rows. `LexicalBinderClosure` derives the finite lexical request domain and exact visited row exposure. `LexicalExposureLanguage` derives its exact least language, and `LexicalBoundedBuilder` connects the concrete memoized builder. Runtime binder interning, alpha-renaming, cleanup, and general pruning callbacks remain adapters. `AcceptanceDispatch`, `AcceptanceEffects` and `AcceptanceSoundness` prove the Boolean worker, both caches, adaptive Unknown handling and sound definite verdicts. Truncated runs are not the complete finite denotation. |
| Refinements: `Refinement.Evaluate`, `Expression`, `Verdict`, `LiquidFixpoint`, `Denotation`, `Automaton`, `Template` | `CoreFormula`: exact integer semantics, simplification, substitution and free names. `FullSyntax`: all current constructors, sorted/quantified interpretation, actual substitution counterexample, exact successful-lattice fragment extraction. Verdict laws, first-formal aliases in `Holds`, and exact template restriction. | Raw-AST sort validation, primitive target theories, serializer/solver IO and complete refinement-evaluator correspondence. Full syntax substitution, alpha-renaming, simplification and target lowering are proved. `FormulaExecutable` connects structural comparisons to the simplifier. `RefinementValidation` proves finite reachable structural validation and all signed path endpoints. `SolverAdapter` proves source query preparation, declaration coverage, response handling, and returned-verdict soundness under correct external solver answers. `SourceFormula` instantiates the full guard backend; `SourceEntailment` proves name-identification transport and its necessary negative-verdict boundary. |
| Pruning: `Refinement.Prune` | `Observation` and `ObservationGraph`: executable path plans, exact sparse views, graph variants, all-finite-term specialization coverage, homogeneous refinement decisions and successful guard discharge. `PruneSchedule`: source decision loop, ambiguous-actual restoration, unknown error, recursion bypass, bottom-up cache/binder driver. | `PruneCorrectness` proves the full successful mutual schedule and cache invariant. `PruneCandidates` derives candidate semantics and Unknown restoration from concrete specialization. `PruneMemo` and `PruneDependencies` prove split-memo coverage and dependency-local cache transport. `PruneReads` proves the repaired recursive gate. `SourceGuardRefinement` derives decided sparse/complete agreement from unambiguous source tables. `SourceGuardPlan` proves actual trie/read adequacy and `FullGuardPrune` connects every current Guard constructor to exact successful conflict-free specialization. `SourceScopeQueries`, `SourceSortedQueries`, and `SourceHoldsQueries` prove full mathematical query transport with nested scopes and generated declarations. The repaired ambiguity gate restores original guards or reports compiler uncertainty. `FullGuardPruneStable` removes the conflict-free condition for the historical whole-guard entry under an explicit backend transport contract. `SourceBooleanBridge`, `BooleanGuardPrune`, and `BooleanGuardCompile` lift these scoped results to the repaired public entry. `SourceConstraintConjunction.edgeView_conjoin` derives the actual constructor product guard law. `PartialReductionCaller` derives exact completed inherited equality descent, smart binder rebuilding, execution-bound stability, and repeated whole-node fixed-point preservation. Primitive interned/path/binder adapters, recursive termination, and operational solver correspondence remain. A checked ambient-name collision in the supplied Z3 adapter prevents unconditional exact verdict transport. |
| Similarity/minimization: `Refinement.Minimize` | Guard classification and finite productivity/below-check. `MinimizeSchedule`: directional similarity queries, dominator resolution, source rewrite schedule, read checks, snapshots and fallbacks. The historical schedule has a checked root-nonemptiness counterexample. The repaired schedule installs root representatives and proves their acceptedness from clear-transition productivity. | `SimilarityWithin` proves exact ordered eligible pairs, inference results, and candidate counts. `MinimizeParentIndex` proves the complete indexed schedule equals the full-table schedule and preserves parent metadata through root insertion. Concrete map/interned conversion and validation correspondence remain. Exact language preservation is not its representative-selection contract; the repaired root invariant is now proved for every completed schedule, with the old failure retained as historical evidence. |
| Integer counting: `Refinement.Lattice` | Concrete linear/formula compilation and exact indicators; normalization and terminating feasibility; all-degree Faulhaber sums; actual piece splitting, repeated elimination, stored levels and cumulative polynomials; derived initial support/metadata; integral nonnegative count; zero count iff no solution; exact integer implication decisions. `LatticeSelect.points_api_exact`: actual cumulative polynomials and stored levels give exact natural counts and the full successful-source decoder bijection. Generator point closure is exact. `SearchCost`: logarithmic cumulative-query count. | `LatticeRetry` proves named failures, bounded reorder retries, exact points and definite verdicts. `LatticeSingleton` proves exact successful one-variable singleton detection. Binding freshening, typed syntax/container/machine-index correspondence and remaining supported-input error adapters remain. |
| Ranked core: `Index`, `Ranked.Internal`, `Ranked.Internal.Decoder` | `DistinctRank` and `System`: exact distinct-term Fin n bijection, requested term probabilities and optimization transport. Mixed-radix laws; exact finite plan decoding and normalization. `SizedRank`: inverse ranks and class positions. `PlanVariants`: nested shared/sized constructors, derived counts/order, valid and invalid ranks. | `DecoderDispatch` derives actual n-ary table ordering, exact branch/local-rank selection, and concatenated-member lookup. `DecoderDispatchCost` proves logarithmic comparison cost from actual balanced compilation. `DecoderMachineBounds` derives safe signed modular arithmetic for cumulative offsets, product-size scans, local narrowing, and fused decoding. Callback validation, physical maps, host conversion, indexed-source correspondence and runtime shared storage remain. |
| Size tables: `Ranked.Internal.Size`, `Gen.Internal.Table`, `Gen.Internal.Recursive`, `Gen.Internal.Recur` | Finite sparse convolution and zero-size coverage. `RecursiveSize`: exact node-count language/count/decoder and bounded probabilities. `MinimumSize`: terminating least-size computation. `TablePosition`: actual bottom-up child/state ranking, derived prefixes/offsets, last-successful selection, exact acceptance/replay. | `RecursiveSource`, `MinimumWitness`, and `PublicRecursion` derive guarded single-knot class records, minimum witnesses, probability recurrence and dispatch. `GroupedMinimum` proves finite-key discovery. `SourcePlanPositions` derives complete finite constructor position dispatch, valid class ranks, safe original outcome selection and retained callback certificates. `SourcePlanPartition` derives both position inverses, unique class membership, a complete finite rank permutation, and exact total size counts. `RecursiveUnambiguous` and `SourceCyclicAutomaton` derive distinct cyclic FTA class ranks and bottom-up inverses from the actual public overlap gate and row prechecks. Concrete containers, nested heterogeneous runtime families and lazy representation remain. |
| Sampling: `Ranked.Internal.Sampler`, `Ranked.QuickCheck`, generator QuickCheck modules | Exact rational laws; executable integer-mass conversion, equal-weight grouping, source cumulative binary search and ticket decoding; weighted/uniform/map/product/rejection constructors; structural offsets, finite product indexes, machine-range preconditions and bounded sampler composition. | `SamplerDispatchCost` derives logarithmic ticket-table comparisons. `SamplerMachineBounds` derives exact group, midpoint, and payload word arithmetic from checked compilation. Concrete Map/array and GHC conversion correspondence, backend laws and retry liveness, recursive sample-index productivity, heterogeneous facade wiring. `SamplerReplay`, `FiniteSource`, and `RecursiveRecord` derive complete finite and bounded plain-recursive records and exact distributions. |
| Shrinking: `Ranked.Internal.Shrink`, inspection functions | `Shrink`: all finite constructors, global least-size member with least-rank tie break, strict rank decrease, non-growing size, exact smaller-size traversal, uniqueness and order. | Concrete cached size-index and callback correspondence; lazy infinite traversal. |
| Static generation: `Gen.Internal.Static`, `Automaton`, `Flat`, `Support`, `Types` | `GeneratorCombinators`: explicit weighted members, indexed counts, product counts and quotient/remainder selection, map/pay/atomic distribution laws, complete inverse queries. `PublicResult`: inspection errors. | `FiniteSource` and `SamplerReplay` derive whole and exact-size decoder/sampler records. `SupportTerms` proves source term callbacks. `SupportGraph` and `SupportJoin` prove singleton, keyed-family, restriction and n-way join languages. `SupportClosing` proves exact finite layer closing through nested choices; `SymbolRelabel` proves cyclic graph relabelling under local guard transport. `SupportAlternatives` and `SupportSpineAlternatives` prove exact closing of grouped roots and correlated function spines. `RecursiveSupportBoundary` proves the repaired private recursive boundary. `StaticCheckedRanks` derives true-flag replay certificates for the finite constructor algebra. `CheckedRankQueries` proves the actual public filter and least-rank query from local callback certificates, completeness, and order. `StaticRankQueryExact` derives finite candidate completeness, strict order, bounds, and exact public inversion. `CompositeCheckedRanks` derives finite chain/join/frequency/enumerated certificates, completeness, order, and bounds. `RecursiveCheckedRanks` derives product/choice/pay certificates and exact all-view bounded/global inversion for a complete guarded unary family. `DatatypeDecoder` derives hash-collision-safe full-term restoration, exact codec composition, and comparison bounds. The constructor-probe modules derive terminating productive witnesses, safe FIFO contexts, and complete accepting-transition coverage. `RecursiveTermAlignment` derives equal counts and exact value/term rank alignment for typed single-knot products, choices, maps, pays, and labels, including every bounded prefix. `RecursiveTermMass` and `RecursiveRankMass` derive the full value, term, and rank probability fields before duplicate values are projected. `RecursiveSourceUnfolding` and `RecursiveSamplerUnfolding` derive the full ordered class and sampler knot equations. The `RecursiveCallback*` modules derive terminating all-view inverse queries, exact class and bounded global ranks, source order, and distinct positions for the single-knot binary-choice body algebra. Local finite callback laws have static and atomic producer proofs. `RecursiveNaryChoice` derives the local arbitrary-branch class selector and complete checked inverse from child producer laws. `RecursiveNaryBody`, `RecursiveNaryMass`, `RecursiveNaryRankMass`, and `RecursiveNarySource` cover arbitrary-branch forward bodies and flat ranked field equations. `StaticSamplingDispatch` and `BucketMergeDispatch` extract all finite flag branches. `RecursiveNaryFields`, `RecursiveNaryInverse`, `RecursiveNaryCandidates`, `RecursiveNaryCausality`, and `RecursiveNaryQuery` derive complete n-ary inverse callbacks, source knot equations, bounded/global ranks, order, and distinctness. `KeyedTermAlignment`, `KeyedTermMass`, and the `KeyedCallback*` modules derive independent keyed value/term fields, full simultaneous source equations, and complete bounded/global inverse queries. `KeyedTermCodes` derives total unique source key positions and exact restricted support. Flat n-ary keyed choices, recursive grouped joins, nested runtime families, inspection callbacks, and imported-record correspondence remain. |
| Grouping and joins: `Gen.Internal.Bucket`, `Grouped`, `Join`, `Chain`, `Query` | `GeneratorCombinators`: executable sorted-key partitions, size ordering, conditioned joins, bucket mass restoration, relation-test hoisting, member inverse queries and branch-weight policy. `SizeMass`: class algebra. `MassRetention`: general observed atomic product probabilities and unchanged recursive policy. | `RecursiveGroupFilter` derives exact recursive key filtering, ordered effects, errors, and unchanged retained records. Map/Seq/order representation, heterogeneous n-way argument wiring, other group effects, and recursive join adapters remain. |
| Symbolic generation: `Gen.Internal.Symbolic` | `Symbolic`: executable distinct-intersection signed map, arbitrary-overlap union count, equality contexts, resolution, substitution, constructor expansion, projection, singleton shortcut and block ranking. `SymbolicDriver`: full bounded mutual count/normalize/expand/select/rank driver and graph/context caches. | `SymbolicCounter` now proves all six counter functions and both caches. `SymbolicIndicators` derives signed graph semantics from compiled guards and guarded rows. `SymbolicMeaning` derives successful acceptedness, rank inverses and injectivity. `SymbolicCounterTotal` derives sufficient execution bounds and total stable results for all six counter functions. `SymbolicComplete` proves total decoding and the full distinct `Fin n` index. `SymbolicStructuralBudget` derives semantic and budget laws from acyclic copied rows. Pure interned readback, allocation rank and old-language stability are proved. `SymbolicAllocatedGraph` closes smart-constructor cleanup and allocation-derived indexing. `SymbolicTotalAPI` adds total inverse/rejection. `SymbolicCacheIndependence` proves worker answer independence and concurrent shared-cache validity. `SymbolicPublicAdapter` proves count-once public callbacks and all rank/empty errors. `SymbolicSelectionCost` bounds outer count requests by output size and constructor vocabulary; `SymbolicUnionCost` bounds exponential overlap preprocessing. `SourceSymbolicIndex` and `SourceSymbolicStableIndex` connect actual successful guard compilation to one fixed exact source index and requested term weights. `FiniteAutomatonDriver` and `SourceFiniteAutomaton` derive the mixed compact/symbolic cache driver, source equality parsing and normalization, overlap gate, structural termination, exact public ranks and empty errors. Concrete runtime correspondence remains. |
| Refinement compilation: `Gen.Refinement.Internal.Compile`, `Witness` | Alias, retained-size, finite closure and per-size mass foundations. `SizeTransport`: paid constructors preserve class/mass alignment. `RecipeCompile`: actual recipe routing, root/spine checks, error precedence, hole consumption, integer closure and source atomic-pair metadata counterexample. | `ObservationMass` and `GuardedSampling` derive complete observation products, guard filtering, counts, replay and conditioned distribution. `IntegerLiteral` derives singleton parsing, counting and decoding for every literal. `IntegerTermCodec` proves whole-term rank/decode inverses from actual filling/extraction. `IntegerLabelCodec` instantiates source labels; `OpenIntegerReaders` derives bare-spine hole counts and coordinate order. `IntegerTermViews` proves all three term-view inverses for each original outcome. `ImportObservations` derives exact observation maps, partition coverage, disjoint groups, and decoder composition. `StaticCandidateRanks` derives finite constructor candidate discovery and exact combined point ranks. `OpenIntegerKeys` proves coordinate renaming, disjoint tuple blocks, joined formulas, and product counts. `StaticCompositeCandidateRanks` covers chain/join callbacks and arbitrary-length choice offsets. `CompiledIntegerSpine` derives actual singleton keyed-join terms, hole counts, and exact ranks from generated recipes. `LatticeDeclaredNames` derives formula scope from successful parsing. `ParentIntegerSettlement` derives finite parent counts and conditioned masses from actual child tables and parent filtering. `IntegerCandidateEnvelope` derives candidate-oracle completeness from actual decoder order. `DefiningTerm` derives exact singleton semantics for accepted measures. `ParentGuardFormula` derives parent guard translation from those target refinements. `OpenChoiceRouting` derives finite point weights, branch retention, and source error precedence. `GroupPositions` derives complete first-position lookups for finite and recursive keys. `OpenGroupComposition` derives repeated-key finite merge, heterogeneous widths, parent-labelled ranks, retained counts and conditioned mass. `OpenGroupedApplication` derives finite multi-group applicative pair enumeration, unique concatenated keys, actual JoinN terms, complete filled ranks, coordinate splits, count/mass products, and parent settlement. `FinalObservationRanks` and `FinalObservationMass` derive final observation regrouping, nested frequency wrappers, all view preimages, rank-aligned mass records, normalized event probabilities, and errors. `FiniteSizeFields`, `FiniteSizeSampling`, `FiniteSizeSeries`, `IntegerSizeClosure`, `OpenGroupedSize`, and `FinalSizeFields` derive finite class positions, actual weight callbacks, sparse mass arithmetic, integer-width shifts, and final merge sampling. General recursive composition, arbitrary imported-record flag dispatch, and runtime record wiring remain. |
| Public APIs: `CFTA`, `Equality`, `Refinement`, `Gen`, `Gen.Equality`, `Gen.Refinement`, `Gen.Do`, `Gen.Label`, `Gen.Sig`, `Gen.Error`, `Inspection`, `Ranked` | All 66 modules and export families mapped in `API-COVERAGE`. `PublicResult`: finite/recursive/opaque distinctions, rank errors and exact decided witness filtering. `System`: constrained grammar, distinct Fin n ranks and requested probabilities composed. | Close wrapper, error and callback correspondence to the handwritten models. Member ranks and distinct-term ranks have different contracts. |

### Arbitrary-branch mutual-family integration

`KeyedNaryAlignment`, `KeyedNaryMass`, and `KeyedNarySource` preserve complete
ordered source records for flat mass-weighted choices in mutual families.
`KeyedNaryFields`, `KeyedNaryInverse`, `KeyedNaryCausality`, and
`KeyedNaryQuery` prove all-view candidate and bounded inverse laws.
`KeyedNaryDispatch` distinguishes a bare singleton merge from raw choice.
`KeyedGuards` and `KeyedNaryGuards` connect original occurrence metadata to
the public size and term-growth checks. All eleven modules, including the
kernel examples, are imported by the aggregate dependency audit.

This closes the flat-choice adapter gap for the typed keyed algebra. Local
finite-leaf contracts, arbitrary runtime builder schemas, concrete key
representations, and Haskell extraction remain explicit boundaries.
See [the family notes](notes-keyed-nary.md) and
[the guard notes](notes-keyed-nary-guards.md).

### Current equality and binder normalization

`ConstrainedRecursionGate` models `meetsConstrainedMu`, including same-path
unfolding of open unconstrained binders. A total worker is checked under an
explicit decreasing unfolding rank; the actual source rank is still open.
`BinderSelfUnion` proves exact least-language preservation of the root
self-reference filter. `EqualityIdentityMemo` verifies identity equality,
structural ordering, and memoized descent/conjunction under cache invariants.
See [the current equality notes](notes-current-recursive-equality.md).

### Recursive joins and current sparse decisions

The `RecursiveJoin*` modules now compose heterogeneous and nested joins
inside full typed mutual-family bodies. They derive independent record
projections, exact ranked probabilities, minimum tables, source equations,
mutual inverse callbacks, and public bounded decoder preimages. Candidate
bounds/order/distinctness include false flags. Public queries preserve
ascending distinct ranks under local finite-leaf callback contracts.
`RecursiveJoinGuards` derives family guards from the original public
occurrence metadata. Full support/inspection and weighted-flag assembly,
missing term fields, and arbitrary runtime schema changes remain open.

The current sparse evaluator differs from the older blanket-ambiguity
policy. `SourceEnclosingRenames` records upstream's precise check.
`SourceSubstitutionPrecedence` adds the proved same-scope repair.
`CurrentGuardPrune` models the evaluator-first candidate loop and proves
exactness for unambiguous specialization cells. General accepted ambiguous
sparse-to-complete transport is still open.
The older `FullGuardPrune`, `BooleanGuardPrune`, and memoized candidate
adapters use a more conservative upfront check. Their preservation results
do not establish that missing current-source transport law.

## Evidence and boundaries

Each completed component must record the relevant Haskell definitions, the
Lean definitions and theorems, required representation invariants, and the
remaining connection to callers. Kernel checking must reject omitted proofs
and nonstandard axioms. Regression artifacts support source correspondence;
they do not replace its proof.

External components require explicit contracts: the Lean kernel, primitive
arithmetic/container behavior, the Haskell runtime and compiler, solver
answers, and random-bit generation. These contracts must not assume an
internal algorithm's desired result. Machine bounds, callback validity,
concurrent cache behavior, and termination must be addressed at their actual
use sites. This list records proof boundaries; it does not declare them
verified or exempt all code that uses an external component.

## Remaining proof obligations

- Connect the checked lattice retry and equality normalization drivers to
  physical maps, arrays, name conversion and machine indexes.
- Connect proved symbolic allocation, smart constructors and shared-cache
  public callbacks to concrete runtime representations. Total count/select/rank
  and the distinct index are proved.
- Connect finite lexical binder instances and the proved full nested rebuilding
  worker to runtime interning caches, stable identity readback, and host storage in the proved initialized enumeration driver. Finite memo traversal, two-stage interning,
  terminal fast paths, and bounded row-language invariants are now derived. Soundness, completeness, rendering, and
  sufficient stable execution bounds are now proved.
- Connect caller state, binder allocation, and substitution to the checked
  union-find, observation, and finite graph algorithms.
- Prove recursive pruning and remaining heterogeneous recursive compilation
  terminate. Cyclic graph-to-binder construction now has a totality proof
  under complete cycle marking.
- Prove the explicit unbounded identity fixed point used by pruning for
  eligible finite equality reductions. The public equality worker itself
  now performs one pass. The nested source witness in
  [notes-finite-reduction-growth.md](notes-finite-reduction-growth.md) shows
  why finite languages, semantic descent, and the leaf guard bound do not
  prove this result. No nonterminating acyclic source case is known here.
- Establish the remaining runtime, external solver, random-source, and codec
  correspondences at the stated boundaries.

The intended pipeline has composition theorems. The current implementation
has operational models, a complete module inventory, focused source checks,
and counterexamples. These are separate deliverables. The unresolved internal
proof obligations above prevent a whole-implementation verification claim.
