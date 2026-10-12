# microcfta formal model

[The system specification and current findings](SYSTEM.md) describe the
language, distinct-term index, distribution, and optimization contracts.
[API-COVERAGE.md](API-COVERAGE.md) maps all 66 source modules and exported
function families. [COVERAGE.md](COVERAGE.md) records proof obligations.

Current base: `origin/microcfta` at `d7f7c11`, including the merged
core-formula extension at `9ad319d`. The branch retains its earlier repairs
and adapts their mass transport to paid constructors. Earlier reports retain
their original source hashes and describe historical snapshots.

The model proves constrained grammar compilation, complete bounded language
enumeration, a distinct-term bijection with `Fin n`, requested term
probabilities, counted decoding, and component optimization laws. The source
models include core and quantified formula syntax, symbolic counting,
small-arity terms, size classes, shrinking, public failure behavior, and the
construction, enumeration, pruning, minimization, and symbolic drivers.
`System.grammar_bijection` and `System.grammar_probability` compose the
reference grammar, FTA, index, and distribution results.

Fourteen recorded implementation failures now have source repairs and checked
regressions: quantified substitution, observed atomic weights, accepted root
representatives, open recursive unions, pruning through open nested binders,
closing grouped private alternatives, recursive term boundaries, and grouped
function spines, unsafe sparse substitution decisions in pruning and compilation,
unbounded conjunction growth during equality reduction, and interference between
independent semantic guards, repeated expansion of recursive equality
domains, explicit unions lost during observed imports, and rejected recursive
observation groups. Historical counterexamples remain
separate from the repair theorems. See [SYSTEM.md](SYSTEM.md).

The later source proofs include complete symbolic count/select/rank execution
and its distinct-term bijection, compiled guard indicators, three-valued cached
acceptance, typed single and mutual recursive sampling records, enumeration
soundness, completeness and final rendering,
successful recursive pruning, total cyclic binder construction, exact support
constructors, and the full indexed-array equality normalization loop. See the [symbolic notes](notes-symbolic-semantics.md),
[indicator notes](notes-constraint-indicators.md), [acceptance notes](notes-acceptance.md),
[recursive source notes](notes-recursive-source.md), [keyed source notes](notes-keyed-source.md),
[enumeration notes](notes-enumeration-driver.md), [binder notes](notes-binder-language.md),
[array notes](notes-array-union-find.md), [pruning notes](notes-prune-correctness.md),
[lattice retry notes](notes-lattice-retry.md), [cyclic conversion notes](notes-binder-compile.md),
[equality reduction notes](notes-equality-reduction.md),
[exact enumeration notes](notes-enumeration-exact.md),
[support graph notes](notes-support-graph.md), and
[actual-table notes](notes-actual-quotient.md).

This is not a claim that the whole Haskell implementation is verified. The
Lean algorithms are handwritten. Some complete driver invariants, concrete runtime
representations, and external contracts remain explicit in the coverage
ledger. A proved reference algorithm does not prove its Haskell adapter.

Toolchain: Lean 4.34.1. Dependencies: Lean's bundled `Std` and `Lean` libraries.

## Build and inspect

From this directory:

```sh
lake build
```

`lean-toolchain` pins the installed version. The package needs no external Lean
dependencies. In the restricted WSL environment, the `elan` wrapper failed while
querying its default channel. The installed binary worked:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake build
```

The default target imports every proof module and runs
[`MicroCFTA/Audit.lean`](MicroCFTA/Audit.lean). The audit checks the transitive
axiom dependencies of every theorem in the `MicroCFTA` namespace, including
generated and private theorems. It permits only `propext`, `Classical.choice`, and
`Quot.sound`. A placeholder proof, a native evaluation axiom, or a project
axiom makes the build fail. Temporary public and private theorems with `sorry` verified that the audit
rejects `sorryAx`. The negative probes are outside this project.

## Proof map

New end-to-end and source correspondence modules are described in
[SYSTEM.md](SYSTEM.md) and [API-COVERAGE.md](API-COVERAGE.md). The table below
also retains the earlier component proof anchors.

| File | Principal results |
| --- | --- |
| [Language.lean](MicroCFTA/Language.lean) | `mem_enumerate_iff`, `accepts_iff_eventually_enumerated`, `accepts_intersect_iff`, `pathEquality_correct`, `strict_prefix_paths_not_equal`, `equality_sharing_preserves_terms` |
| [Probability.lean](MicroCFTA/Probability.lean) | `split_pair`, `pair_split`, `uniform_tickets_probability`, `frequency_probability`, `eventMass_condition`, `regrouping_preserves_distribution`, `join_group_pair_probability` |
| [Integration.lean](MicroCFTA/Integration.lean) | `samples_probability`, `event_probability`, `accepted_has_rank`, `rank_is_accepted`, `accepts_iff_eventually_positive` |
| [Guards.lean](MicroCFTA/Guards.lean) | `evaluate_supports`, `splitGuard_preserves`, `groupByKey_cover`, `partition_discharge_preserves`, `independent_holds_sound`, `holds_alias_counterexample` |
| [Lattice.lean](MicroCFTA/Lattice.lean) | `signed_correct`, `normalize_divisor`, `project_pair`, `firstMaximum_unique`, `firstMaximum_exists`, `intervalSum_antiderivative` |
| [Counterexamples.lean](MicroCFTA/Counterexamples.lean) | `similarity_guard_counterexample`: the original language is nonempty, the rewritten graph remains structurally productive, and its accepted language is empty at every depth. |
| [Holds.lean](MicroCFTA/Holds.lean) | `firstNames_lookup`, `aliasPairs_correct`, `compiledQuery_iff`: repaired aliases represent exactly one value per mentioned path, in both polarities. |
| [Decoder.lean](MicroCFTA/Decoder.lean) | `count_correct`, `decode_correct`, `decode_normalize`, `decode_binary_fusion`, `countAt_correct`, `compiled_coverage`, `compiled_probability_normalized` |
| [Minimization.lean](MicroCFTA/Minimization.lean) | `classified_guard_preserves` and the historical rejected-representative counterexample |
| [Sized.lean](MicroCFTA/Sized.lean) | Atomic repair correctness, source-size counterexamples, concrete partition coverage, and proposed size-retaining reconstruction laws |
| [Productivity.lean](MicroCFTA/Productivity.lean) | `finite_stability`, `reachClosure_correct`, `productive_correct`, `checked_representative_has_accepted_term`, `RootDeletion.root_deletion_counterexample` |
| [SizeMass.lean](MicroCFTA/SizeMass.lean) | `classWeights_total`, `classWeights_positive`, `mergeWeight_associative`, `split_merge_probability`, `split_product_probability`, and the atomic-pair mass counterexample |
| [Sparse.lean](MicroCFTA/Sparse.lean) | `addSparse_ordered`, `mulSparse_ordered`, `valueAtSize_mulSparse`, `sparse_split_correct`, `seeded_product_correct`, and zero-size prefix counterexamples |
| [ZeroSize.lean](MicroCFTA/ZeroSize.lean) | `splitPairs_exact`, `closePoints_exact`, `closePoints_has_rank`, `closePoints_size_count`, `zero_lag_no_finite_count` |
| [UnionFind.lean](MicroCFTA/UnionFind.lean) | Exact compression and union classes, termination, size metadata, allocation-domain closure, and `union_satisfies` |
| [Cache.lean](MicroCFTA/Cache.lean) | First-writer readback, pure memoization, interleaved identity allocation, canonical keys, and shard equivalence |
| [Fragments.lean](MicroCFTA/Fragments.lean) | Completion-preserving hole resolution, slot intersection and assimilation, and exact combined union/assimilation constraints |
| [RecursiveSize.lean](MicroCFTA/RecursiveSize.lean) | Exact node-count enumeration, count-recurrence uniqueness, size-major decoding, sparse convolution correspondence, and bounded run probabilities |
| [MinimumSize.lean](MicroCFTA/MinimumSize.lean) | Asynchronous relaxation, proved convergence, least accepted node counts, and safe omission of empty or smaller size classes |
| [Observation.lean](MicroCFTA/Observation.lean) | Concrete path-plan construction, sparse lookup, exact keys, and derived guard homogeneity |
| [ObservationGraph.lean](MicroCFTA/ObservationGraph.lean) | Cyclic-graph specialization coverage, exact stored observations, and `selectSpecialized_discharges_guard` |
| [LatticeRank.lean](MicroCFTA/LatticeRank.lean) | Exact cumulative-count binary search, both lexicographic rank/select inverses, finite tuple coverage, and a verified integer-closure table |
| [LatticePolynomial.lean](MicroCFTA/LatticePolynomial.lean) | Sparse polynomial normalization, addition, multiplication, powers, partial substitution, and constant extraction |
| [Faulhaber.lean](MicroCFTA/Faulhaber.lean) | Exact source Bernoulli recurrence and the discrete-antiderivative identity for every degree and every rational argument |
| [PolynomialSum.lean](MicroCFTA/PolynomialSum.lean) | Concrete `sumOver` equals the finite integer-interval sum, including negative endpoints and empty intervals |
| [PolynomialSupport.lean](MicroCFTA/PolynomialSupport.lean) | Variable removal, preservation of prior removals, and exact constant extraction after all variables are absent |
| [LatticeLinear.lean](MicroCFTA/LatticeLinear.lean) | Integer linear arithmetic, sparse-map invariants, supported expression parsing, and integer/rational evaluation correspondence |
| [LatticeNormalize.lean](MicroCFTA/LatticeNormalize.lean) | Exact conjunction normalization, valid maps, no added variables, and elimination of constant inequalities |
| [LatticeBound.lean](MicroCFTA/LatticeBound.lean) | Executable unit-coefficient extraction, exact inequality semantics, and variable deletion |
| [LatticeFeasible.lean](MicroCFTA/LatticeFeasible.lean) | Actual minimum-cost variable choice, projection, termination by distinct-variable count, and sound rejection |
| [EqualityTrie.lean](MicroCFTA/EqualityTrie.lean) | Exact path construction, prefix checks, sorted distinct enumeration, descent, and arity bounds |
| [EqualityNormalize.lean](MicroCFTA/EqualityNormalize.lean) | Canonical connected components, congruence generation, contradiction detection, completed bounded normalization, and strict-extension range correctness |
| [SizedRank.lean](MicroCFTA/SizedRank.lean) | Size-major/class-rank inverses, source/map/choice/application positions, and exact sparse product offsets |
| [TablePosition.lean](MicroCFTA/TablePosition.lean) | Bottom-up term ranking, derived transition prefixes, last-successful overwrite semantics, acceptance equivalence, and exact replay |
| [PlanVariants.lean](MicroCFTA/PlanVariants.lean) | Nested shared/sized plans, size/rank conversion, derived counts, and omission of zero-count classes |
| [Sampler.lean](MicroCFTA/Sampler.lean) | Rational-to-integer masses, cumulative binary ticket decoding, exact weighted events, sampler composition, and bounded constructors |
| [EqualitySaturation.lean](MicroCFTA/EqualitySaturation.lean) | Exact short-circuit trie cardinality and descent; finite-model saturation bound |
| [EqualityTermination.lean](MicroCFTA/EqualityTermination.lean) | Unconditional termination of canonical equality saturation and exact total normalization semantics |
| [EqualityModel.lean](MicroCFTA/EqualityModel.lean) | Constructive finite models for accepted fixed points; rejection iff no finite model exists |
| [LatticePiece.lean](MicroCFTA/LatticePiece.lean), [LatticePipeline.lean](MicroCFTA/LatticePipeline.lean) | Actual bound traversal and piece construction, exact weighted splitting, normalization/feasibility filtering, and variable deletion |
| [FiniteSum.lean](MicroCFTA/FiniteSum.lean), [LatticeCount.lean](MicroCFTA/LatticeCount.lean) | Unique finite-support sums, exact repeated elimination, and final constant extraction |
| [LatticeSigned.lean](MicroCFTA/LatticeSigned.lean), [LatticeFormula.lean](MicroCFTA/LatticeFormula.lean) | Concrete signed simplification, all integer relations, polarity and Boolean compilation, and n-ary traversal/fold correspondence |
| [LatticeInput.lean](MicroCFTA/LatticeInput.lean), [LatticeDecision.lean](MicroCFTA/LatticeDecision.lean) | Derived initial metadata/support/indicator, integer nonnegative counts, and zero count iff no satisfying assignment |
| [LatticeLevels.lean](MicroCFTA/LatticeLevels.lean), [LatticeInterval.lean](MicroCFTA/LatticeInterval.lean), [LatticeCumulative.lean](MicroCFTA/LatticeCumulative.lean) | Stored elimination levels, exact floor-division intervals, cumulative polynomial construction, and exact clipped counts |
| [LatticeAPI.lean](MicroCFTA/LatticeAPI.lean) | Actual point-count constructor, unreachable nonintegral error, and exact integer implication decisions |

Detailed correspondence and limitations are in
[language notes](notes-language.md), [probability notes](notes-probability.md),
and [guard notes](notes-guards.md). [State notes](notes-state.md) describe
union-find, interning and memoization. The [coverage ledger](COVERAGE.md)
records later progress and all remaining implementation obligations.

`Lattice.lean` corresponds to `Refinement/Lattice.hs` as follows:

- `signed_correct` verifies polarity propagation, conjunction products, and
  inclusion-exclusion for Boolean formulas. Lists represent signed-map entries.
- `normalize_divisor` verifies division of a linear inequality by a positive
  common divisor, including floor division of a negative offset.
- `tightest_offset` and `opposite_inconsistent` justify two normalization steps.
- `project_pair` verifies one Fourier-Motzkin projection step.
- `firstMaximum_exists` and `firstMaximum_unique` verify the strict tie rule
  for a selected lower bound. The upper-bound rule follows by negating values.
- `intervalSum_antiderivative` verifies telescoping over intervals that can
  start at negative integers. Its discrete-antiderivative equation is a premise.

The later modules prove the general Bernoulli/Faulhaber construction,
terminating feasibility recursion, formula-to-count pipeline, and cumulative
polynomial sums. `LatticeSelect` now connects the stored cumulative polynomials to exact
section counts and the recursive ranker. `LatticeRetry` proves the named-error
and variable-order retry policy. Concrete `Map` storage, scoped binding,
recursive graph conversion, and Fixpoint serialization remain boundaries.
Full formula freshening and typed syntax lowering are proved in the later
`Formula*` modules; see [formula correctness](notes-formula-correctness.md).

## Meaning of the main theorem

`Language.Accepts` is an independent inductive relation on finite trees.
`Language.enumerate` computes bounded Cartesian products and checks each guard
on its complete tree. The main language theorem proves their equivalence.
A Lean leaf has height one; Haskell depth `d` corresponds to Lean fuel `d + 1`.
Finite terms and finite transition lists suffice. The state graph can be cyclic.

The integration theorem normalizes one ticket per enumerated run. A term with
several accepting runs receives the sum of their masses. Thus the theorem
establishes uniformity over runs, not distinct terms. It does not assert that
arbitrary Haskell generators use this distribution. The separate probability
module proves weighted-distribution identities with explicit preconditions.

The SMT solver and concrete refinement evaluator are outside the language
proof. Guards have a supplied Boolean interpretation there. `Guards.lean`
states the atomic-decision and observation requirements. `Observation` and
`ObservationGraph` now derive coverage and homogeneity from executable sparse
plans and graph specialization. The full substitution algorithm is proved.
`PruneCandidates` proves ambiguous Unknown restoration. `PruneCorrectness`
proves the successful recursive driver under named primitive laws. Concrete
interning, binder adapters and recursive termination remain obligations.

Other remaining boundaries include recursive binder conversion, concrete
interning and union-find callers, lazy size-table execution, machine-integer
conversions, callback contracts, the random backend, and concrete shrinker record wiring.
The state algorithms, finite size recurrences, and lattice binary search have
checked executable proofs. The strict-smaller relation is covered by the
size-retention proofs. The Lean definitions are handwritten algorithms. There
is no verified translation connecting all Haskell code to them.

## Papers

The term semantics follows the supplied LTA paper's Figure 6 and the ECTA
paper's finite-term denotation. ECTA reduction requires exact language
preservation. LTA similarity minimization deliberately removes terms and needs
a weaker representative-preservation property. The current root-deletion
counterexample violates even nonemptiness preservation.

The supplied LTA appendix's Lemmas 2 and 3 have proof headings without proof
arguments. They are not used as axioms. The proofs here also do not formalize
the paper's source-language typing judgment or assume that arbitrary library
functions satisfy their refinements.

Source PDF SHA-256 values:

```text
lta.pdf  f3a84b08cfce95747dac5148f28a9092115bfe3144880ca13e2258531a1f9463
ecta.pdf 34572866be0bc8e86a546f712ffb2666fe641d133417a895ecbdee5d8f6e1ebf
```

## Validation

- The complete Lean package builds. The axiom audit passes.
- All earlier repaired cases and the new counterexamples run inside `nix-shell`,
  with Z3 for the public cases.
- Existing suites pass after the five repairs: 274 core, 190 generator, and 135
  refinement examples; 599 total, zero failures. The added cases extend existing
  suites. The final fresh-name counter change also passes the focused formula
  suite and the repaired Z3 capture probe.
- Fourmolu accepts the reproductions. Cabal-gild accepts both audited packages.

The Haskell commands run from the repository root:

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal build lib:microcfta lib:microcfta-generator -j1'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=microcfta -package=microcfta-generator lean/repro/Counterexamples.hs'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=microcfta -package=microcfta-generator lean/repro/RemainingFindings.hs'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=microcfta -package=microcfta-generator lean/repro/CurrentFindings.hs'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test microcfta:unit-tests microcfta-generator:gen-tests microcfta-generator:refinement-tests -j1 --test-show-details=direct'
```

The host compiler path resolves the existing Nix/GHC `-lgmp` linker failure on
this WSL host. The reproduction is a standalone audit artifact. It does not
add a package test suite.

## Next proof obligations

1. Connect the checked finite sampler records to every heterogeneous recipe and
   support callback. Atomic observed masses are repaired and proved.
2. Connect the proved root-representative schedule to concrete graph conversion
   and guard validation. The root deletion defect is repaired.
3. Connect proved single and mutual recursive records and size invariants to
   heterogeneous families and lazy runtime tables.
4. Connect rich sparse guard observations and concrete interned identities to
   the proved pruning and complete symbolic index drivers.
5. Connect the checked lattice eliminator and rank/select implementation to
   scoped binding and concrete container adapters.
6. Establish an implementation correspondence through a translation, extraction,
   or a narrower verified core. Differential tests can support this work but
   cannot replace the correspondence proof.
