# cfta formal model

Current source: `TharkunAB/cfta`, `origin/main` at `239feb64`.
Continue on `formalize`; publish completed checkpoints to `origin/formalize`.
The former remote remains as `microecta-legacy`. The Haskell packages are
`cfta`, `cfta-generator`, `cfta-ghc`, and `decision-model`.
Public `Data.CFTA.*` modules and Lean namespace `MicroCFTA` retain their names.
The Lake package is `cfta`.
Root [HANDOFF.md](../HANDOFF.md) supersedes historical descriptions below.
The [upstream refresh](notes-main-refresh-20261015.md) preserves every proof.
Core and generator definitions are unchanged. Decision-model and the moved
GHC session library remain outside formal source coverage. All six Haskell
suites pass, with 687 examples plus the golden suite. The strict build,
formatting, and metadata checks pass for all four packages.
The [actual outer-worker proof](notes-outer-worker-demands.md), `7369264b`,
retains both first-child receipts and their returned warm states. A general
one-row law makes those child completions necessary for successful parent
bodies under any callback. It composes with the typed result-thunk busy trace.
Next integrate actual result-memo keys and memo state with the recursive
worker. This supersedes the earlier first-incomplete-worker target below.
The [closed caller cycle](notes-outer-caller-cycle.md), proved in `eed062bd`,
returns to the original physical root with empty inherited constraints after
two actual local prefixes. Its observed physical-key relation is not well
founded. The retained source certificate passes. Cold and warm full-pass
calls time out. The typed result-thunk instantiation in `6e4d477d` reaches
busy with neither result completed. The actual-worker note now supplies
its monadic first-child necessity laws. No production algorithm is repaired.
This supersedes unconditional caller-rank targets below. The kernel result does not prove GHC divergence.
The audit passes 1,894 jobs and 49,138 theorem dependency checks.
The [source boundary checks](notes-origin-boundaries.md) refute inherited
literal conjunction closure and a local maximum-path bound. Retained Haskell
prefixes also refute physical absorption of a repeated intersection factor.
The latter kernel identity candidates remain explicitly unverified drafts.
These are finite boundary checks, with no infinite-growth or termination
claim. Exact small normalization receipts retain the actual source result.
The [finite physical constraint inventory](notes-constraint-inventory.md)
remains proved for checked successful public calls, with exact language,
both source gate memo receipts, and stable full-state replay. Inherited
records and actual node construction need separate analysis. The caller
cycle now supersedes that physical-key rank target.
The [ordinary-height counterexample](notes-constraint-origins.md) still applies.
The [closed warm completion proof](notes-closed-warm-completion.md) gives finite
local execution at arbitrary closed warm scopes under reached word checks.
The [inherited Region proof](notes-inherited-plain-completion.md) gives finite
outer execution for equality-free regions with any inherited payload.
The [Sized comparison](notes-canonical-upstream.md) remains current. Exact
classes, finite size execution, sequence, and both rank inverse contracts
retain their source definitions. UVar and synthesis orders remain separate.
This paragraph supersedes generic factor and inherited-closure candidates.
Older next-target statements below are historical where superseded here.
The [inherited edge proof](notes-inherited-edge.md) derives actual physical
constraint combination and trie descent, indexed child obligations, exact
callback observations, and direct equal-arity edge rebuilding. Concrete native
local narrowing composes with that inherited continuation. The pointwise node
callback remains an explicit induction hypothesis. The outer node/row worker,
modifyNode fast path, and actual Mu reconstruction remain next. Stable six-stage
bounds apply to a fixed callback; they do not prove whole-caller termination.
This paragraph supersedes older inherited payload and child-continuation targets.
The [public guarded-edge proof](notes-public-native-edge.md) derives annotation
preservation through actual general merging, captured targets, first forcing,
shared edits, gate selection, required paths, class folds, and guarded interning.
The complete concrete guarded native edge pass narrows publicly and has exact
public input/output language under inherited satisfaction. Original normalized
syntax derives finite source execution, both memo certificates, stable stage
bounds, and eventual bounded-array agreement. The actual inherited caller and
full reducePartially traversal remain next. This paragraph supersedes older
complete-pass annotation targets. Repeated-pass termination, GHC scheduling,
and extraction remain separate.
The [normalized annotation proof](notes-normalized-annotations.md) discharges
all concrete source guard laws at the existing independent PCS meaning.
It proves public agreement on normalized annotations, derives annotation heaps
from original construction, and preserves them through actual stored-body
compilation and optional binders. The concrete source edge entry has exact
PCS output/public input meaning. Public output readback still needs native
and shared-edit annotation heap preservation. This paragraph supersedes older
unrestricted guard-law next targets. GHC extraction remains separate.
The [guarded-edge proof](notes-guarded-edge.md) now derives actual accessor
readback, valid physical records, literal original-guard reconstruction, stable
six-bound and bounded-array execution, and original closed source completion.
Independent edge language is exact under inherited satisfaction and the
existing local guard-constructor contracts. Concrete normalized constructor
laws are proved. Their restriction to actual reached guards remains next;
unrestricted laws on malformed raw payloads are not established. This paragraph
supersedes older guarded-edge next targets. GHC extraction remains separate.
The [complete native one-pass proof](notes-native-one-pass.md) now derives
actual prechecks, physical record selection, required paths, native folds,
and final propagation in one worker. It has checked two-way graph agreement,
stable six-bound answers, eventual bounded-array agreement, independent
language preservation, and original source completion with both gate memo
certificates. Actual guarded-edge rebuilding and guard/payload readback are
next. This paragraph supersedes older combined one-pass worker targets.
GHC scheduling and extraction remain separate.
The [selected class-fold proof](notes-selected-class-fold.md) now composes
actual gate/required stages, original physical records, fresh class captures,
finite native right folds, and one final empty propagation. Stable five-bound
worker agreement and no loss of class-satisfying terms are proved. Original
closed construction supplies the selected live-branch entry. The combined
one-pass worker and guarded-edge language are next. This paragraph supersedes
older class-fold next targets. GHC scheduling and extraction remain separate.
The [shared class-edit proof](notes-shared-class-edits.md) now derives actual
first force, exact target reuse, finite simultaneous edit completion, and
stable five-bound function/graph agreement. Compiled original class paths
retain every accepted class-satisfying term. Actual selected-class fold and
structural empty propagation are next. This paragraph supersedes older shared
forcing next targets. GHC lazy scheduling and extraction remain separate.
The [demanded class-target proof](notes-demanded-class-targets.md) derives
actual projection/merge operands, interleaved first-seeded native target folds,
finite stable four-bound execution, and original class-subterm preservation.
Construction receipts derive captured target scope and no loss of class terms
through native edits. Shared target forcing and full class-pass composition
remain open. This paragraph supersedes earlier standalone target construction
and merge next targets.
The [finite general merge proof](notes-merged-finite.md) now derives general
comparison and merger completion, stable identical full caches at larger
bounds, and original closed source-language inclusion. It uses actual fresh
Mu allocation and source order. Shared target forcing and full class-pass
composition remain open. This paragraph supersedes older completion targets.
The [general merged proof](notes-merged-general.md) derives independent
comparison inclusion, exact child-selection union language, and successful
merge coverage with complete semantic cache preservation. Original construction
and actual getPath composition derive source entry. Its general completion
target is now proved above. Older next-target statements below are historical
when this paragraph supersedes them.
The [scoped native edit proof](notes-native-edits.md) now derives full native
state preservation, finite edit completion, exact retained target language,
and stable three-bound worker agreement. Coherent physical classes have
exact original-path readback. Constructed target receipts now supply its
captured scope in the proof above.
The [scoped native target proof](notes-native-target-fold.md) now derives finite
warm native target folds, exact intersection-list language, and target-then-leaf
narrowing. General projection retains the actual domain and both memo tables.
The simultaneous edit composition now has its scoped proof above.
The [general projection proof](notes-general-projection.md) now derives finite
stable getPath execution on arbitrary closed nested Mu/Union inputs, exact
source closed-union language, and accepted-subterm inclusion. It retains
actual reads, full final caches, and signed missing-position behavior.
Scoped native callback composition and merged targets remain open.
The [public entry proof](notes-native-public-entry.md) derives finite actual
entry execution, exact independent root-language readback, and complete
optimized/reference query-record equality. It includes direct empty/open
returns, exact distinct node-count classes, size order, and both term inverses.
Normalized original annotations and reached cache capacity remain explicit.
The [common API proof](notes-sized-api-laws.md) now applies the complete
specification to original-map reference, optimized dispatch, and actual bounded
solver-decided traces. The [general cold entry proof](notes-general-cold-liquid-entry.md)
now derives actual normalized validation and complete encoded queries from
repaired construction. It retains the real arity failure before solver work.
The [closed source theorem](notes-source-closed-sized.md) now derives construction
and all three exact query paths at the original expression's guarded least
language. Reference and optimized paths return identical records and errors.
The [general unfolding-rank proof](notes-general-unfold-rank.md) now derives
strict minimum free-occurrence rank decrease for every actual repaired open
Mu unfolding. It includes arbitrary nested Mu and root unions. Prepared-plan
retention derives nonempty reconstruction for live siblings. Actual execution
retains every cache invariant needed by later unfoldings. The concrete
certified read adapter gives a total gate decision and finite instrumented
evaluation at every finite path. Original source construction derives its
initial representation premises. The [stateful gate proof](notes-stateful-gate.md)
now threads actual returned caches through ordered edge and path scans.
It proves finite class evaluation, exact graph/execution correspondence,
and uniqueness of both Boolean decisions and final caches. Original source
construction derives finite traces. Coherent outer-unfold memo hits and misses
have exact constructor readback. The [memo graph and source read proof](notes-memo-gate-predicate.md)
now carries unfolding memos through complete ordered graphs. It installs the
actual visited-node `crush` read and proves its finite distinct identity
inventory. Node and class source entries have no supplied whole-node predicate.
The concrete predicate memo also has exact hit/miss and growth laws.
The [exact fold and both memo proof](notes-source-crush-both-memos.md) now
characterizes every physically reached ordinary edge, including shared
canonical records and root unions. A false fold has a reached failing edge.
Complete gate graphs now carry both actual memos and retain exact finite
source execution. The [complete class filter](notes-ordered-class-selection.md)
now retains both memo tables and one ordered receipt per class occurrence.
Derived gate replay gives exact pure selected-class readback in the retained
final cache and connects the existing one-pass theorem. The
[physical entry proof](notes-physical-class-order-entry.md) now derives the
installed source sort schedule, exact trie/set comparison, safe prechecks,
and actual parent-array normalization before selection. A checked raw-class
comparator cycle explains why the physical merge schedule is retained.
The [Needed compiler and cycle repair](notes-needed-head-repair.md) now
prove exact signed trie construction and independent complete-path meaning.
The kernel checks constructor-row exposure and empty least language for the
raw self binder. Eight source traversals now use that exposure. All 645 Haskell
examples pass. The original stutter witness and reproduction remain unchanged.
The source child-adjustment fold now has exact lookup and conditional forest
meaning. The actual arity check derives every normalized child position.
The [physical required-path worker](notes-required-execution.md) now derives
finite stable execution, actual cache effects, and exact graph correspondence
for arbitrary closed source inputs. Its source entry includes retained raw
binders. The complete worker has kernel fixtures for the raw cycle and early
row rejection. The [independent head-language proof](notes-required-head-language.md)
now identifies actual head normalization with the input guarded least language.
A finite future cache is a proof witness; runtime conversion is unchanged.
Both semantic probe heaps survive the full required-path graph. Normalized
paths derive nonnegative trie keys at every depth. The
[complete filter proof](notes-required-filter.md) now derives exact independent
node and forest languages from actual graph execution. It retains the missing
top-level child boundary and proves both pure-pass required-operation laws.
Closed source selection derives its unchanged constructor cache and composes
with required-path execution, including both actual memo receipts. The
[simultaneous edit proof](notes-edit-execution.md) now retains signed trie
compilation, callback branch priority, finite traversal from stored leaf
contracts, exact graph agreement, and stable complete returned caches.
Independent edit conditions agree with the signed child fold. The
[edit-language proof](notes-edit-language.md) now derives actual output
languages, exact original nonoverlapping path readback, and coherent physical
class edit conditions. Actual native intersection supplies immediate leaf
cache effects and exact narrowing with captured-target scope and checked
word ranges explicit. Next compose scoped callbacks and actual projection
and merged targets through the caller. Native lazy scheduling, open contexts,
containers, and extraction remain separate.
[The Lava paper note](notes-lava.md) records relevant prior art and its source,
solver, and termination limits. The [occurrence-cost note](notes-occurrence-costs.md)
records the full weighted source callback/probe correspondence used here.
All old proofs, fixtures, and marked drafts remain.

[The system specification and current findings](SYSTEM.md) describe the
language, distinct-term index, distribution, and optimization contracts.
[API-COVERAGE.md](API-COVERAGE.md) maps all 77 source modules and exported
function families. [COVERAGE.md](COVERAGE.md) records proof obligations.

Current base: `origin/microcfta` at `7989e91a`, including the merged
core-formula extension, the optimization changes, and the merged findings
repairs, bounded import fallback, and shared row adapter through PR #115. Benchmark programs,
datasets, and workload specifications are excluded from formalization.
The [shared row note](notes-shared-rows.md) covers finite extraction, dense
numbering, canonical order, minimum sizes, cyclic query laws, and the custom-key
tie counterexample. Ordinary native intersection construction, dispatch,
completed memo provenance, and shared productivity are now proved. One
productive stored knot has actual unfolding and shared exposure. General
recursive construction remains open. See
[physical construction](notes-physical-intersection-rows.md).
The [bounded import note](notes-bounded-import.md) records the preceding work
and its remaining native correspondence boundaries.
Local repairs reject uncertain identity replacement
and payload queries of unfinished recursive occurrences. Grouped recursion
also rejects discovery tables that disagree with the final body. The
rebase retained every proof and reproduction while retiring superseded
source patches. Earlier reports retain their original source hashes and
describe historical snapshots.

The later liquid review found quantified capture from distinct names with
the same external SMT spelling. Repair `73223201` encodes every solver-facing
name injectively. The [solver name note](notes-solver-name-encoding.md) records
the Lean/native counterexample and the checked codec, preflight, quantified
semantics, and complete public liquid composition. All 635 existing Haskell
examples pass after the repair. The closing audit passes **1,180 build targets
and 39,689 theorem dependency checks** at proof checkpoint `9207c2cf`.

The [finite map Sized proof](notes-sized-finite-keys.md) now derives the
actual raw-map reference, decided, and optimized paths, including canonical
order, finite class execution, all four queries, and both inverse laws.
The original state type need not be finite.
[Weighted selection](notes-quickcheck-frequency.md) derives the actual
QuickCheck backend and verifies the safe midpoint repair `a8b32869`.
All 206 generator examples passed again after that isolated repair.
The [equality root proof](notes-equality-nested-unary-root.md) completes both
ancestor edits and bounded iteration for its fixed unary/two-atom fragment.
Root [HANDOFF.md](../HANDOFF.md) gives the remaining targets and exact logs.
All work is local. Benchmark formalization remains excluded.

The model proves constrained grammar compilation, complete bounded language
enumeration, a distinct-term bijection with `Fin n`, requested term
probabilities, counted decoding, and component optimization laws. The source
models include core and quantified formula syntax, symbolic counting,
small-arity terms, size classes, shrinking, public failure behavior, and the
construction, enumeration, pruning, minimization, and symbolic drivers.
`System.grammar_bijection` and `System.grammar_probability` compose the
reference grammar, FTA, index, and distribution results.

Recorded implementation failures now have source repairs and checked
regressions: quantified substitution, observed atomic weights, accepted root
representatives, open recursive unions, pruning through open nested binders,
closing grouped private alternatives, recursive term boundaries, and grouped
function spines, unsafe sparse substitution decisions in pruning and compilation,
unbounded conjunction growth during equality reduction, and interference between
independent semantic guards, repeated expansion of recursive equality
domains, explicit unions lost during observed imports, and rejected recursive
observation groups, bounded traversal of retained empty binder cycles,
self-dependent measure extraction, recursive open group positioning, and
same-scope identity-replacement precedence, and inconsistent recursive
payload queries during reconstruction, and stale grouped minimum-size tables.
Historical counterexamples remain
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

The source finite and cyclic FTA entry points now derive their distinct-rank
contracts from the actual guard and ambiguity gates. See the
[finite compiler notes](notes-source-finite-automaton.md) and
[cyclic index notes](notes-source-cyclic-automaton.md). Final finite observation
merging also connects ranks to retained probability mass. See the
[observation merge notes](notes-final-observation-merge.md).
The [finite size-field notes](notes-finite-size-fields.md) connect those
records to exact class weights, sparse mass tables, and class samplers.
The [recursive alignment notes](notes-recursive-term-alignment.md) connect
typed recursive value and term indexes at every class and bounded rank.
The [recursive callback notes](notes-recursive-callbacks.md) connect the
actual inverse workers to those tables for the single-knot binary-choice
body algebra, including ordering, uniqueness, and exact ranked probabilities.
The [arbitrary-choice notes](notes-recursive-nary-choice.md) cover the local
ordered list adapter and its recursive child producers.
The [n-ary body notes](notes-recursive-nary-body.md) extend the full forward
compiler, guards, decoder, inverse, and ranked mass fields to arbitrary branch
counts. Their callback proof includes the source knot equation and exact
bounded global rank queries.
The [keyed alignment notes](notes-keyed-term-alignment.md) and
[keyed callback notes](notes-keyed-callbacks.md) extend these results to
finite mutually recursive key families. They retain separate key masses,
actual private member wrappers, and complete per-key global inverses.
The [flat keyed-family notes](notes-keyed-nary.md) extend the mutual-family
results to any finite branch count. They include retained mass, complete
inverse queries, and empty/singleton merge dispatch. The [original guard
notes](notes-keyed-nary-guards.md) derive size and term-growth checks from
label-aware syntax before value lowering.
The [dispatcher notes](notes-static-dispatch.md) cover all finite sampling and
bucket-merge flag branches. The [similarity notes](notes-similarity-within.md)
and [parent-index notes](notes-minimize-parent-index.md) verify the new
minimization optimizations.
The [current equality notes](notes-current-recursive-equality.md) cover the
revised recursion gate, root self-reference removal, and constraint identities.
The [recursive join notes](notes-recursive-join-fields.md) cover nested
heterogeneous join bodies, mutual-family probabilities, full inverse
callbacks, and public bounded queries. The [join guard
notes](notes-recursive-join-guards.md) derive the required family guards
from the original source metadata. The [runtime notes](notes-recursive-runtime.md)
connect source weight flags, optional terms, and query errors to those families.
`RecursiveJoinSupportFamily` derives their shared-binder support languages
from independently compiled term derivations. The [support and inspection
notes](notes-recursive-join-support-inspection.md) describe the separate named
diagnostic graph and its constructor proofs. The [complete-record
notes](notes-recursive-complete-record.md) connect all these fields to one
checked program.
The [fresh-probe notes](notes-interned-fresh-probe-keys.md) separate the
proved nested-binder key cases from the remaining normalization-erasure case.
The [probe provenance notes](notes-interned-probe-provenance.md) derive the
probe premises from constructor traces. The [gate rank
notes](notes-gate-unfolding-rank.md) distinguish lexical termination from
remaining smart-union source cases.

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
a weaker representative-preservation property. The historical root-deletion
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

The current closing evidence is above and in root [HANDOFF.md](../HANDOFF.md).
The following older commands and results remain historical records.

- The complete Lean package builds. The axiom audit passes.
- All earlier repaired cases and the new counterexamples run inside `nix-shell`,
  with Z3 for the public cases.
- Existing suites pass on `de910ea`: 284 core, 194 generator, and 142
  refinement examples; 620 total, zero failures. The log is
  `/tmp/mcfta-scope-precedence-full.log`. Existing scope cases were extended
  for the new evaluator repair.
- Fourmolu accepts the reproductions. Cabal-gild accepts both audited packages.

The Haskell commands run from the repository root:

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal build lib:cfta lib:cfta-generator -j1'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=cfta -package=cfta-generator lean/repro/Counterexamples.hs'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=cfta -package=cfta-generator lean/repro/RemainingFindings.hs'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=cfta -package=cfta-generator lean/repro/CurrentFindings.hs'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test cfta:unit-tests cfta-generator:gen-tests cfta-generator:refinement-tests -j1 --test-show-details=direct'
```

The host compiler path resolves the existing Nix/GHC `-lgmp` linker failure on
this WSL host. The reproduction is a standalone audit artifact. It does not
add a package test suite.

## Earlier proof obligations

Use root [HANDOFF.md](../HANDOFF.md) for the current ordered targets.
The following list retains the earlier broad correspondence scope.

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
