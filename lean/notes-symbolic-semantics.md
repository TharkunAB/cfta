# Symbolic driver semantic proofs

The new modules use the executable definitions in `SymbolicDriver.lean`.
They do not replace the source decoder with a materialized reference index.

## Normalization and solver requirements

`SymbolicNormalization.lean` proves the meaning of successful `inline`,
`follow`, `rename`, `normalizeTarget`, `normalizeObligation`, and `normalize`
calls. `normalize_solution_iff` preserves domain tests, bindings, and all
pending requirements under the compact variable assignment. The proof includes
missing paths, self-equality, operand ordering, sorting, and deduplication.
`normalize_none_rejects` proves that a failed path rejects the old solution.

`normalize_preserves_graph_domains` retains the graph identities in their
original order. `normalize_fresh` proves distinct compact names and a fresh
next-variable supply. `occurs_constructor_reject` proves the actual occurrence
test cannot reject a finite solution. `constructor_obligations_semantics`
proves the constructor decomposition used by `unify`.

`SymbolicSolutions.lean` defines finite live tuples independently of the
counter. `normalize_count` proves exact count preservation under the source's
empty or one-binding normalization invariant. It also proves the independent
product count and the zero-count path and occurrence branches.

`SymbolicBijections.lean` proves that these tuples are distinct and gives a
finite relation cardinality theorem. `SymbolicMerge.unify_variables_count`
uses it to prove the exact delete/intersect/insert/binding update. Other
pending correlations remain in the theorem.

`SymbolicScope.normalize_scoped` proves that successful normalization leaves
only live names in pending requirements. `SymbolicExpansion` uses this result
to extend old assignments with fresh child names without changing earlier
requirements. `expand_component_count` proves a bijection for the exact
sorted-domain, binding, and edge-obligation update. Each raw equality
component has its own selected-variable language. Components can contain
terms rejected by the original guard before signed cancellation. The proof
does not assume these terms belong to the original node language.

## Counts and caches

`SymbolicCounting.lean` proves graph and context cache lookup/store safety
under explicit semantic cache invariants. `countUnion_distinct_terms` connects
the actual stateful signed fold to the number of accepted distinct candidates.
Its recursive edge-count and exact-intersection premises remain explicit.
`solveStep_independent` proves the actual independent-domain product branch.

`SymbolicSignedSolutions.signed_coordinate_count` lifts any pointwise signed
term identity through all other live domains and pending correlations.
`expand_variable_count` applies it to the actual nested union and indicator
loops. `SymbolicEdgeCounts.edgeProblem_count` proves that the exact initial
edge problem counts its raw component terms.

`SymbolicExpansionDriver`, `SymbolicCounterCache`, and `SymbolicUnification`
prove every source branch and its recursive caller invariants.
`SymbolicCounter.counter_correct_mutual` closes the induction for all six
actual functions: `countNode`, `countEdge`, `solve`, `solveStep`, `unify`, and
`expandVariable`. `counter_countSound` discharges the `CountSound` contract
used by the decoder. `cardinality_correct` proves the public count is the
number of distinct accepted finite terms for every successful bounded call.

The remaining graph interface is `CounterMeaning`. It requires distinct
finite graph languages, exact domain intersection, and a pointwise signed
edge-membership identity. That identity uses the actual nested source
coefficients, including every overlap and guard indicator. It does not
assume any counter result. The mutual theorem also takes one fallback term
to construct a total variable valuation for empty independent tuples.

## Source decoder and inverse

`SymbolicSelection.decoder_inverse_mutual` proves that the three actual
selection functions invert through the three actual inverse functions. The
proof covers block skipping, child order, singleton shortcuts, and identical
cache flow. It holds for every successful bounded run. It does not assume
semantic count correctness. The inverse returns the input rank minus the
unconsumed suffix.

`SymbolicBounds.decoder_bounds_mutual` proves the residual stays below the
final graph cardinality, assuming `CountSound`.

`SymbolicMeaning.lean` supplies the semantic composition. Its `FiniteMeaning`
interface requires distinct finite graph languages, exact constructor
conditioning, and subtree projection coverage. Projection need not be exact.
`singleton_decoder_meaning` proves the actual singleton decoder correct.
`decoder_meaning_mutual` proves all constructor and child restrictions retain
the selected subtree and all earlier selections.

`selected_root_exact` derives a singleton final language and residual zero.
`unrank_sound_and_inverse` proves that every successful public decode is
accepted and has its exact original inverse rank. `unrank_injective` excludes
two successful ranks for one term.

`source_rank_bijection` proves every accepted term has exactly one actual
source rank in `Fin n`. Its local `DecodeTotal` premise states only that every
in-range bounded decoder call returns. The later termination modules derive
this premise from structural graph budgets and finite row semantics.

`SymbolicVerified.rows_decode_correct` and `rows_rank_bijection` now compose
these results with the full mutual counter theorem and
`SymbolicIndicators.counterMeaningFromRows`. The inputs are graph rows,
compiled guards, intersection, conditioning, and projection semantics. There
is no assumed counter-correctness or cache-correctness contract.

`SymbolicDecoderTotal` proves constructor coverage for the actual
projection/map/dedup/sort candidate worker and full singleton decoder
termination. `SymbolicBlocks` proves that distinct constructor blocks
partition the accepted root language. `SymbolicSelectionTotal` proves
termination of the actual progressively restricted child loop and general
selector by strict descent in accepted subtree height.

`SymbolicComplete.rows_full_index` gives the complete composed result. There
is one finite bound after which actual public cardinality equals `n`, every
rank in `Fin n` decodes, and every accepted term has exactly one actual rank
with the exact `rankOf` inverse. No count-correctness, cache-correctness,
component-count, or decoder-totality premise remains.

`SymbolicGraphView.view_full_index` removes the semantic graph premises.
It derives a finite list by enumeration at a structural budget and removes
duplicate terms. It proves the list exact from independent finite-run
acceptance. `OperationRows` checks the identities of copied synchronous
product rows, template rows, and projected row unions. Its row checks permit
duplicate removal and order changes. These structural checks derive exact
intersection and conditioning and subtree projection coverage.

`SymbolicStructuralBudget.acyclic_full_index` also derives the complete
counter budget. `structuralValue` computes one plus the largest child-budget
sum among all rows. `structural_intersection` proves that copied product
rows cannot increase either operand's budget. The remaining inputs are
operational row-copy identities, compiled guard interpretation, and a
topological rank for every structural child reference. No finite-language,
language-operation, count, cache, or decoder-totality law is assumed.

`SymbolicInternedView` connects immutable row keys to the pure interning
state. `intern_rows` proves exact canonical readback. Reservation,
installation, and interning preserve acyclicity when all new child references
were already issued. Numeric identities then give the topological rank.
`growth_exact` proves that a later cache snapshot preserves every old closed
graph language. The theorem applies to issued constructor identities.
It does not identify an unissued lookup with the source's distinguished
`EmptyNode`, and it does not cover recursive thunks or machine `Int` overflow.

These results reduce the concrete representation obligation. They do not yet
construct `OperationRows` for the Haskell allocation and normalization
pipeline. That pipeline can remove empty rows and normalize constraint
representations. Its copied raw rows must be connected to the actual stored
rows with the corresponding cleanup and guard-equivalence proofs.

`SymbolicNormalizedRows.normalized_full_index` permits those row removals.
An omitted row must have a false guard or an empty copied child. The proof
derives exact acceptance by term induction and budget bounds from structural
row inclusion. No language equivalence is assumed for the cleanup itself.

`SymbolicProductRows.closed_full_index` additionally models the closed
self-intersection shortcut. It handles `intersect node node = node` as a
separate operational branch. This is necessary: returning the operand omits
nonempty cross rows, so those rows cannot be justified by emptiness.

`SymbolicAllocatedGraph.allocated_full_index` replaces the topological-rank
input with finite constructor allocation histories. Each reservation checks
that its child identities already exist. First-writer installation preserves
the invariant. Different rows can come from different finite snapshots. The
numeric identity order still gives one global rank. The theorem retains
explicit copied-row identity and compiled-guard checks. It does not assume
that the allocation history has pre-enumerated accepted terms.

`SymbolicHashJoin` models the source singleton-prepending bucket loop.
`build_exact` gives the exact reversed right bucket, including repeated
occurrences. `hashJoin_member` proves that every equal-key pair is emitted
and no unequal-key pair is emitted. `hashJoin_length` retains multiplicity.
The map is keyed by the complete symbol key; the proof does not equate a
hash collision with key equality.
`clusters_permutation` also proves that restoring grouped source edge lists
only permutes a duplicate-free node's alternatives. It cannot remove or
repeat an edge.

`SymbolicCanonicalOrder` models the source recursive operand swap. One swap
suffices to reach the minimum/maximum identity pair. Both call directions
then use the same complete key and result, without requiring a commutative
body. Valid first-writer memo tables preserve that result. Equal stored
identities also identify the exact payload key, by the interning invariant.

The remaining Haskell correspondence checks are concrete. They include the
identity map for the distinguished `EmptyNode`, typed cache selection,
constructor payload readback, canonical operand reordering, constraint
normalization on copied guards, and the concrete runtime table operations.
The pure row and allocation theorems state the checks precisely. They do
not turn those runtime checks into machine-checked GHC implementation proofs.

`SymbolicEqualityBridge` now connects normalized PCS classes to the symbolic
common-subtree interpretation. The nontrivial-class invariant is necessary:
raw PCS singletons impose no condition, while reflexive `Same` guards require
an existing path. Completed equality normalization preserves the indicator.
`conjoined_constraint_score` proves that recompiling the normalized source
conjunction gives the exact product of both input indicators. It includes
the `combineGuards` truth and identical-operand simplifications. The equality
normalization proof retains its explicit successful-completion condition.

`SymbolicSignedPaths` models the source signed path lookup and `fitsArity`.
It proves that a failed arity check cannot remove a valid equality-constrained
term and that successful checked paths decode to natural indices unchanged.
`packedLookup_exact` connects the signed lookup to packed term storage.
For guards that retain negative indices, `encode_lookup` and `encode_class`
use an out-of-range sentinel under a proved constructor-arity bound.
`accepted_arityBound` derives that bound from graph rows. The proof explicitly
rejects negative reflexive paths. A concrete theorem shows why applying
`Int.toNat` without checking the sign changes semantics.

`SymbolicRankSoundness` proves the reverse membership direction of the actual
inverse API. Every successful child and constructor rank retains a nonempty
language whose terms have the requested subtree. `rankOf_sound` proves that
returning a rank implies membership. `rankOf_rejects_nonmember` proves that a
completed inverse on a nonmember returns `Nothing`. `rankOf_checked_inverse`
also proves every returned rank is in range and decodes to the supplied term
once the full finite decoder bound has been reached.

That reverse direction needs exact projection at the empty root path.
Conservative projection alone would permit a singleton shortcut on an empty
root language. `closed_rootProjection` derives the stronger root fact from
the actual cleaned row-union view. This is a proof-interface requirement,
not a defect in the source root projection.

`SymbolicRankCache.ranking_preserves` covers all inverse results, including
`Nothing` after partial traversal. Rejected terms can share their count cache
with later calls. `SymbolicRankTotal.rankOf_eventual` proves stable successful
termination for every supplied finite term. Its induction descends through
that term and through finite constructor lists. `rankOf_eventually_rejects`
therefore rejects nonmembers without an execution-success premise.

`SymbolicTotalAPI.allocated_total_api` composes the complete result from
constructor allocation histories, copied operation rows, and compiled
guards. One common bound covers cardinality and every valid finite index.
Every supplied finite term has a further bound for its inverse answer.
`Nothing` then means nonmembership. A returned integer is in range and its
actual decode returns that exact supplied term. All these results use the
same executable counter, decoder, and inverse workers.

`SymbolicSmartRows` proves the source node constructor's empty-child filter
and edge deduplication preserve row membership. It also proves that an edge
removed by the singleton-node emptiness check has numeric indicator zero.
`source_union_filter_exact` therefore justifies the extra empty-intersection
test in Haskell `countUnion`. `SymbolicSourceUnion` proves weighted sums
invariant under coefficient-map permutation and proves cache-safe signed
traversal in any order. These theorems compare numeric results and cache
validity. They do not claim that the list model and Haskell `Map.toList`
produce identical cache traces.

## Progress and freshness

`SymbolicProgress.lean` proves that whole-variable intersection and variable
expansion strictly decrease a summed structural graph budget. It proves that
normalization preserves this budget, insertion and expansion preserve distinct
live names, and a fresh expansion cannot create a cyclic binding.

`SymbolicWork` gives explicit sufficient bounds for substitution and path
following. It derives a strict substitution budget from the source's empty
or single acyclic binding. `SymbolicNormalizationWork.normalize_work` proves
that the complete actual normalizer does not increase context and path work.
`SymbolicNormalizationTotal.normalize_total` proves successful normalization
at fuel at least twice its weighted pending work plus one. It requires
explicit scope for bindings and pending requirements.

`SymbolicCallProgress.union_edge_budget` proves that every generated signed
intersection key retains the source graph's structural child budget.
`SymbolicWellFounded.counter_calls_wellFounded` covers all six recursive
control branches. Its lexicographic measure uses the summed graph budget,
pending context and path work, and control phase. It includes constructor
decomposition and the constructor-variable swap. `GraphBudget` derives the
structural graph premises for explicit finite acyclic graphs and their
intersection, restriction, and projection operations.

`SymbolicFuel` proves exact successful normalization outputs remain unchanged
at larger bounds. `SymbolicInputScope` proves that initial edge problems,
variable merges, and constructor expansions retain every name needed by the
next normalizer. `SymbolicEventual` combines stable bounds for finite state
traversals. It preserves the exact final cache as well as the count.

`SymbolicCounterTotal.counter_eventual` transfers the well-founded relation
to the actual six bounded functions. Every valid call returns one fixed value
and final cache at every sufficiently large bound. It holds for arbitrary
initial caches. `cardinality_total_exact` combines this termination result
with the full semantic counter theorem. Public cardinality eventually returns
the exact number of distinct accepted finite terms.

The decoder termination proof does not require a structural decrease for
conditioned projected identities. It uses the independent finite language's
subtree height. Structural budgets are needed for counter termination on each
identity created by the graph operations. The pure identity allocation and
graph-budget bridge now has the structural results described above. The
concrete Haskell normalization and allocation correspondence remains separate.

These modules build with Lean 4.34.1. The proofs use no added axioms, `sorry`,
or native evaluation. The finite-rank existence proof uses Lean's standard
classical choice principle.
