# Finite multi-group applicative compilation

`OpenGroupedApplication` follows the applicative branch of
`compileOpenSpine`, its all-True `relateGroupsM` call, `pairBucket`, and the
successful singleton paths of `mergeComponentsByKey`. It includes arbitrary
finite numbers of input key groups and recursive composition of these
applicative sources. It does not assume that a grouped product preserves
terms, counts, or weights.

The source distinguishes a key position from a coordinate. A grouped child
contributes one position even if its key has several integer coordinates.
`compileKeys_positions` derives the complete coordinate-count list from the
bare recipe compiler. `keys_arity` derives position count from the independent
source syntax. `reader_split` proves that the source `take spineArity` key
operation gives exactly the function reader's coordinate width. Thus groups
can have different widths without moving argument coordinates into the
function reader.

`Source` contains three concrete cases. `generated` uses the actual compiled
bare-spine record. `repeated` uses the homogeneous key group proved by
`OpenGroupComposition`. `app` retains the actual component index and both
complete child sources. Primitive integer observations use one opaque
identity, since each primitive has the same root observation shape. Repeated
observed groups retain their complete `Signature` identity. This is an
observation-identity projection, not a second implementation of the source
observation maps.

`Selected`, `select`, and `select_exact` connect an independent constructor
relation to the executable decoder. A pair uses the actual
`SupportJoin.joinTerm` with a nullary `Pure` operation and two argument-key
wrappers. Its right original cardinality is the rank radix. `selected_bound`
and `selected_exists` prove the full interval. `selected_valid` and
`selected_width` derive the fill shape and coordinate count at each level.
`evaluate` follows the same source value-reader splits. `evaluate_total`
proves that every admitted original and complete point decode to a value.
User maps need no injectivity assumption.

`pairs` follows the source ordered list comprehension. `pairs_get` and
`applyBuckets_get` identify every pair's exact component index as
`functionBucket * numberOfArgumentBuckets + argumentBucket`. This index is
assigned before result-key sorting. It is separate from the original member
rank inside that bucket and from the subsequent integer-point rank.

`append_injective` proves the decisive map invariant. The left key-position
count is fixed in one family. Equality of concatenated result keys therefore
implies equality of both input keys. `applyBuckets_keys_unique` derives
unique result keys from the source input maps. `partition_keys_unique`,
`grouped_keys_unique`, and `repeatedBuckets_unique` derive those initial map
invariants from the actual repeated-key grouping algorithm.
`applicative_singleton_path` proves that each resulting positive group takes
`mergeBucketGroup`'s singleton fast path. No general merge behavior is
assumed for this applicative call.

`mergedBuckets` models result-key sorting and outer mass normalization.
On the proved unique positive-key domain, the source's per-key merge retains
the same complete static records. `merged_sources_perm`, `merged_pair_source`,
and `merged_count` preserve every indexed bucket pair. `merged_arity` and
`merged_keys_unique` establish the same invariants for the next applicative
level. `merged_totalCount` gives the complete original-member product count.
The comparator parameter is the source key comparator. The permutation
laws do not need to assume a different rank order after sorting.

`joinedKey_app` uses the actual concatenated key list.
`productPoints_append` and `joinedKey_points` derive the optional count
product, including unknown propagation. `joinedTuples_append` derives the
function-then-argument tuple order. `application_domain` uses actual
successful primitive lattice tables to prove that the combined formula
accepts exactly the complete Cartesian tuple domain. It also derives the
stored product count and absence of duplicate coordinate tuples. Coordinate
name separation comes from `OpenIntegerKeys`.

`candidates` follows the recursively constructed source callbacks. The pair
callback uses the actual pure operation, binary argument chain, and private
`JoinN` view dispatch. `candidates_complete` derives discovery after filling
for generated, repeated-key, and applicative sources. `points_complete`,
`points_sound`, and `every_closed_rank` compose those callbacks with the
actual point ranker and its final term-view check. `closed_value_total`
derives the value reader's length requirement from the actual lattice
points. No abstract callback completeness postcondition replaces these
constructor proofs.

`rankDistribution` records the source global outcome masses. Generated
originals have one unit-mass outcome. Repeated groups normalize their actual
incoming original masses. Applicative sources multiply the two internal
rank distributions. `rankDistribution_count` and
`rankDistribution_probability` prove the corresponding count and probability
invariants on the source-success domain. Outer bucket masses are separate.
`applyBuckets_totalMass` derives their product total, and
`normalized_pair_mass` gives the exact source normalized share. Normalization
changes no key, private term, or original rank. The size-conditioned sampling
field modified by `pairStaticWithMasses` is separate from this global outcome
mass. Its arithmetic and record transport remain in `SizeMass`,
`SizeTransport`, and the existing source-record modules.

`settle` executes the finite closed-parent point query and zero-count drop
for all source key positions. `settle_fields` derives the exact returned
table and retained share from success. `closed_count`,
`settled_every_rank`, and `settled_value_total` connect that actual record to
counts, complete ranks, and value decoding. `parent_event` uses the source
child count records and successful child tables to derive the exact mass
retained by the parent conditions. `settled_conditioned` gives the normalized
finite conditioned distribution.

The final parent label is also modeled. `parentCandidates` follows
`labelOutcomeTerms`, including forwarding to the inner `LabelledView`.
`parent_points_complete` and `parent_points_sound` include point filling and
full view validation after that label. `settled_parent_ranks_exact` combines
the executed settlement with actual successful `exactLabel` substitution.
The matcher property comes from `IntegerLabelCodec.exactLabel_matches`.
Equal visible terms can retain several original member ranks. These theorems
do not assert an inverse for arbitrary decoded values.

The remaining source adapter after this finite applicative and parent
settlement fragment is final observation regrouping and its nested frequency
wrappers. Arbitrary imported static sources and other public constructors
still need their own initial source-record correspondence. This module does
not silently extend the generated/repeated/applicative syntax to them.
Guard translation is separate in `ParentGuardFormula`; solver errors and
unsupported observations still stop the source before this finite path.
Readable-name error wrapping, machine integer bounds, graph interning, and
recursive or unknown-point sampling are not reimplemented here.

Validation: `lake build MicroCFTA.OpenGroupedApplication` passes all 96 jobs
with the pinned Lean 4.34.1 toolchain. The module has 73 theorems and uses no
admitted declaration or native proof evaluation. No production Haskell,
Cabal files, tests, global reports, or audit files changed for this module.
