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

Source baseline: `origin/microcfta` at `d7f7c11`. This includes the merged
core-formula changes at `9ad319d`. The current semantic specification and
implementation findings are in [SYSTEM.md](SYSTEM.md). All 66 source modules
are inventoried in [API-COVERAGE.md](API-COVERAGE.md).

The branch now repairs all four recorded failures. Formula substitution
preserves bound application names. Observed atomic members retain their
within-size weights. Minimization installs and checks accepted root
representatives. Open unions retain epsilon operands. Existing suites pass
273 core, 190 generator, and 135 refinement examples. Historical
counterexamples remain checked against their explicitly named baseline
models. The positive repair theorems are separate.

## Coverage ledger

| Area and source modules | Checked foundation | Remaining work |
| --- | --- | --- |
| Term/path semantics: `Path`, `Term`, `Internal.Tree`, `Generic`, `Simple` | `Language`: finite runs, bounded enumeration, path lookup, equality sharing. `TermRepresentation`: all small-arity constructors, invariant, round trips and lookup. `TermOperations` and `ChildBuilder`: complete indexed construction, edits, preorder traversal and arbitrary folds. `LevelEnumeration`: first-deepest split, exact next level and safe empty-level stopping. `BoundDepth`: exact graph rewrite. `Construction`: nested constrained grammar compilation and finite state closure. `Generic`: terminating finite descriptor discovery, exact language, growth/domain failures and codec rank laws. `Template`: all five patterns and exact graph restriction. | Concrete sequence/hash storage, GHC generic type metadata, binder conversion and public wrapper correspondence. `FTAValidation`, `FromTerms`, `GraphTrim` and `StateMap` now verify the explicit graph operations. |
| Constraints: `Constraint`, `Equality.Constraint`, `Refinement.Guard` | `Guards`: Boolean evaluation and splitting. Concrete trie construction, ordered paths, prefix checks and descent. Canonical connected components and congruence saturation. Unconditional termination, exact semantics, constructive finite models, and rejection iff no model exists. | `ConstraintIndicators` proves the whole supported signed compiler. `ArrayUnionFind`, `EqualityArray` and `ArrayBounds` now prove concrete array workers, complete class iteration/readback/grouping, connected components, finite execution and index bounds. Path-index/canonical-order adapters, physical storage, residual guard decisions and public arity wrappers remain. `EnumerationState` models suspended-path scheduling separately. |
| Interning and recursion: `Interned.Type`, `Interned.Operations`, `Interned.Cache`, `Interned.Memo`, `Interned` | Synchronous graph intersection in `Language`. `Cache`: fresh identities, first-writer insertion, finite interleavings, memo results, sharding with collisions. `Binding`: free-variable dependency, restricted environment cache keys, identity substitution and depth-probe distinction. `BoundDepth`: exact graph copy. `OpenUnion`: historical loss and repaired witness. `EpsilonUnion`: terminating depth-first closure and exact epsilon elimination. | Runtime map/atomic/type-cast correspondence, fresh binder alpha-renaming, recursive conversion and open intersection scheduling. `RedundantEdges` and `GraphRewrite` prove complete row reduction and cyclic graph preservation. `BinderLanguage` proves least-language unfolding and both cleanup cases. Concrete interned binder views must refine the proved finite epsilon graph. |
| Enumeration: `Enumeration`, `Internal.UnionFind`, `Equality.Operations` | `Language`: reference enumeration and sharing. `UnionFind`: exact terminating state operations. `Fragments`: hole resolution, slot intersection, assimilation, and combined union/assimilation assignment semantics. `EnumerationState`: complete fuelled caller, suspended paths, expansion ordering, ancestry cutoff, witness accumulation and rendering, with source behavior examples. | `EnumerationCorrectness` derives storage, allocation, union/assimilation semantics and concrete renderer soundness. `EnumerationSchedule` and `EnumerationDriver` prove the entire caller storage/live-root/alias invariant and completion state. Full assignment simulation, callback soundness, solver correspondence and sufficient execution bounds remain. `AcceptanceDispatch` independently proves the complete Boolean acceptance worker and its caches. Truncated runs are not the complete finite denotation. |
| Refinements: `Refinement.Evaluate`, `Expression`, `Verdict`, `LiquidFixpoint`, `Denotation`, `Automaton`, `Template` | `CoreFormula`: exact integer semantics, simplification, substitution and free names. `FullSyntax`: all current constructors, sorted/quantified interpretation, actual substitution counterexample, exact successful-lattice fragment extraction. Verdict laws, first-formal aliases in `Holds`, and exact template restriction. | Raw-AST sort validation, primitive target theories, serializer/solver IO and complete refinement-evaluator correspondence. Full syntax substitution, alpha-renaming, simplification and target lowering are proved in the seven `Formula*` modules. |
| Pruning: `Refinement.Prune` | `Observation` and `ObservationGraph`: executable path plans, exact sparse views, graph variants, all-finite-term specialization coverage, homogeneous refinement decisions and successful guard discharge. `PruneSchedule`: source decision loop, ambiguous-actual restoration, unknown error, recursion bypass, bottom-up cache/binder driver. | Interned representation/memo correspondence, substitution and equality observations, global driver invariant, recursive fixed-point termination and solver correspondence. |
| Similarity/minimization: `Refinement.Minimize` | Guard classification and finite productivity/below-check. `MinimizeSchedule`: directional similarity queries, dominator resolution, source rewrite schedule, read checks, snapshots and fallbacks. The historical schedule has a checked root-nonemptiness counterexample. The repaired schedule installs root representatives and proves their acceptedness from clear-transition productivity. | Concrete map/interned conversion and validation correspondence. Exact language preservation is not its representative-selection contract; the repaired root invariant is now proved for every completed schedule, with the old failure retained as historical evidence. |
| Integer counting: `Refinement.Lattice` | Concrete linear/formula compilation and exact indicators; normalization and terminating feasibility; all-degree Faulhaber sums; actual piece splitting, repeated elimination, stored levels and cumulative polynomials; derived initial support/metadata; integral nonnegative count; zero count iff no solution; exact integer implication decisions. `LatticeSelect.points_api_exact`: actual cumulative polynomials and stored levels give exact natural counts and the full successful-source decoder bijection. Generator point closure is exact. `SearchCost`: logarithmic cumulative-query count. | variable-order retries, binding freshening, typed syntax/container/machine-index correspondence and full supported-input error mapping. |
| Ranked core: `Index`, `Ranked.Internal`, `Ranked.Internal.Decoder` | `DistinctRank` and `System`: exact distinct-term Fin n bijection, requested term probabilities and optimization transport. Mixed-radix laws; exact finite plan decoding and normalization. `SizedRank`: inverse ranks and class positions. `PlanVariants`: nested shared/sized constructors, derived counts/order, valid and invalid ranks. | Callback validation, n-ary dispatch, machine-index conversion, indexed-source correspondence and runtime shared storage. |
| Size tables: `Ranked.Internal.Size`, `Gen.Internal.Table`, `Gen.Internal.Recursive`, `Gen.Internal.Recur` | Finite sparse convolution and zero-size coverage. `RecursiveSize`: exact node-count language/count/decoder and bounded probabilities. `MinimumSize`: terminating least-size computation. `TablePosition`: actual bottom-up child/state ranking, derived prefixes/offsets, last-successful selection, exact acceptance/replay. | `RecursiveSource`, `MinimumWitness`, and `PublicRecursion` derive guarded single-knot class records, minimum witnesses, probability recurrence and dispatch. `GroupedMinimum` proves finite-key discovery. Concrete containers, nested heterogeneous runtime families and lazy representation remain. |
| Sampling: `Ranked.Internal.Sampler`, `Ranked.QuickCheck`, generator QuickCheck modules | Exact rational laws; executable integer-mass conversion, equal-weight grouping, source cumulative binary search and ticket decoding; weighted/uniform/map/product/rejection constructors; structural offsets, finite product indexes, machine-range preconditions and bounded sampler composition. | Concrete Map/array and GHC conversion correspondence, backend laws and retry liveness, recursive sample-index productivity, heterogeneous facade wiring. `SamplerReplay`, `FiniteSource`, and `RecursiveRecord` derive complete finite and bounded plain-recursive records and exact distributions. |
| Shrinking: `Ranked.Internal.Shrink`, inspection functions | `Shrink`: all finite constructors, global least-size member with least-rank tie break, strict rank decrease, non-growing size, exact smaller-size traversal, uniqueness and order. | Concrete cached size-index and callback correspondence; lazy infinite traversal. |
| Static generation: `Gen.Internal.Static`, `Automaton`, `Flat`, `Support`, `Types` | `GeneratorCombinators`: explicit weighted members, indexed counts, product counts and quotient/remainder selection, map/pay/atomic distribution laws, complete inverse queries. `PublicResult`: inspection errors. | `FiniteSource` and `SamplerReplay` derive whole and exact-size decoder/sampler records. `SupportTerms` proves source term callbacks. Full support graph, inspection callback, imported graph and heterogeneous recipe correspondence remain. |
| Grouping and joins: `Gen.Internal.Bucket`, `Grouped`, `Join`, `Chain`, `Query` | `GeneratorCombinators`: executable sorted-key partitions, size ordering, conditioned joins, bucket mass restoration, relation-test hoisting, member inverse queries and branch-weight policy. `SizeMass`: class algebra. `MassRetention`: general observed atomic product probabilities and unchanged recursive policy. | Map/Seq/order representation, heterogeneous n-way argument wiring, group effects, recursive joins and retained size indexes. |
| Symbolic generation: `Gen.Internal.Symbolic` | `Symbolic`: executable distinct-intersection signed map, arbitrary-overlap union count, equality contexts, resolution, substitution, constructor expansion, projection, singleton shortcut and block ranking. `SymbolicDriver`: full bounded mutual count/normalize/expand/select/rank driver and graph/context caches. | `SymbolicCounter` now proves all six counter functions and both caches. `SymbolicIndicators` derives signed graph semantics from compiled guards and guarded rows. `SymbolicMeaning` derives successful acceptedness, rank inverses and injectivity. `SymbolicCounterTotal` derives sufficient execution bounds and total stable results for all six counter functions. Full decoder totality and interned representation remain. |
| Refinement compilation: `Gen.Refinement.Internal.Compile`, `Witness` | Alias, retained-size, finite closure and per-size mass foundations. `SizeTransport`: paid constructors preserve class/mass alignment. `RecipeCompile`: actual recipe routing, root/spine checks, error precedence, hole consumption, integer closure and source atomic-pair metadata counterexample. | `ObservationMass` and `GuardedSampling` derive complete observation products, guard filtering, counts, replay and conditioned distribution. Heterogeneous recipe/value/support composition, recursive guards and concrete runtime records remain. |
| Public APIs: `CFTA`, `Equality`, `Refinement`, `Gen`, `Gen.Equality`, `Gen.Refinement`, `Gen.Do`, `Gen.Label`, `Gen.Sig`, `Gen.Error`, `Inspection`, `Ranked` | All 66 modules and export families mapped in `API-COVERAGE`. `PublicResult`: finite/recursive/opaque distinctions, rank errors and exact decided witness filtering. `System`: constrained grammar, distinct Fin n ranks and requested probabilities composed. | Close wrapper, error and callback correspondence to the handwritten models. Member ranks and distinct-term ranks have different contracts. |

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

- Connect the checked cumulative ranker to variable-order retries and source maps.
- Derive total decoding for the symbolic driver. Complete mutual count
  correctness, semantic cache preservation and counter totality are proved.
- Connect the verified equality array loop to source path-index allocation,
  inverse path mapping and canonical output ordering.
- Connect caller state, binder allocation, and substitution to the checked
  union-find, observation, and finite graph algorithms.
- Prove recursive pruning and supported recursive compilation terminate.
- Establish the remaining runtime, external solver, random-source, and codec
  correspondences at the stated boundaries.

The intended pipeline has composition theorems. The current implementation
has operational models, a complete module inventory, focused source checks,
and counterexamples. These are separate deliverables. The unresolved internal
proof obligations above prevent a whole-implementation verification claim.
