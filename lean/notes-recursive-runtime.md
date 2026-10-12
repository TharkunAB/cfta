# Recursive runtime flags and optional fields

`RecursiveJoinRuntime` reads source runtime fields beside a complete
`CheckedBody`. Static inputs derive `weighted` from
`StaticSamplingDispatch.hasWeight`. Keyed finite buckets separately check
the presence of retained masses and the atomic total-mass/count comparison.
Join, map, pay, label, and mass-weighted flat choice construct their flags
from their children. A nullary join can promote `massWeighted` into
`weighted`; a singleton same-key merge retains the original record instead.

`joinedTermField_exact` proves that the source operation bind and ordered
argument traversal return exactly the complete checked join callback field
when all term fields are available. A missing field remains absent. No
argument is removed from the term forest. `termField_realizes` transports
the existing local decoder and count proof to every available runtime field.

The bounded sampler adapter gives an executable probability reference for
both runtime branches. Its unweighted branch is uniform over member ranks,
including repeated values. Its weighted branch uses the derived grouped
class sampler. `weighted_family_sampler` connects that branch to the complete
correlated family projection. `bounded_static_dispatch` proves the exact
stored-weight versus uniform Static route. Base runtime field correctness
still belongs to each input constructor. In particular, these Boolean flag
proofs do not assume or establish that every arbitrary input marked false
has a uniform sampler.

`RecursiveRuntimeDispatch` preserves source error order. A probe error
returns through the finite error route. An unused occurrence returns the
original body before knot validation. In the cyclic grouped result, a
sampling-body construction failure precedes the unguarded and empty-family
checks. Weight flags inspect all rebuilt bodies before the output key filter.
The output filter keeps exactly discovered keys with a rebuilt body and a
finite minimum. Term availability stays separate at each key.

`termAt` rejects a negative rank before construction failure and missing
terms. Internal bounded outcome selection checks term availability before
its own rank check. The adapter distinguishes the source internal
missing-member-term failure from an ordinary out-of-range result.
`decoder_no_internal_error` excludes that internal failure for a compiled
decoder plan. Bounding a nonempty value index can succeed without terms;
sampling remains possible while term inspection reports an error.

`familyOutcome_exact` connects runtime term availability to the complete
bounded family decoder. `familyRanks_exact` combines the original public
occurrence guard with that availability check and the complete replay-filtered
inverse. Missing terms return `cannotInspectRecursive`; they do not become
an empty candidate language.

`RecursiveRuntimeOrigins` composes those fields across separate rebuilds.
A typed template retains its source records and recursive keys. Source,
occurrence, map, pay, label, choice, and heterogeneous join constructors
derive the exact primitive origins of term availability and both weight
flags. The probe phase uses placeholders without terms. The term phase
uses placeholders with terms. `term_rebuild_exact` proves that only missing
source term fields can suppress the latter phase; the absent probe fields
do not do so. `family_weighted_origins` and `family_mass_origins` derive
the final family flags from source inputs before output-key filtering.
`family_sampler_from_origin` selects the proved weighted sampler from such
a primitive origin. `member_outcome_exact` derives the final term-presence
check from source term fields, rather than taking it as an independent
per-key availability premise.

`RecursiveUniformRuntime` closes the unweighted rank law. Products enumerate
the full mixed-radix interval. Count-weighted choices concatenate exact
disjoint intervals, including offsets after empty branches. These proofs
retain ranks as well as values. Count-mass groups with uniform ranks remain
so under maps, products, choice, size-split products, and complete recursive
families. The family proof uses size induction and local finite-leaf laws.
`unweighted_family_ranked` proves exact value-and-rank distributions for the
bounded unweighted route, including repeated values.

`RecursiveRuntimeVerified` links the original runtime marker to those laws.
Primitive source records provide a local finite-leaf law only when their
actual weight flags are false. Pure leaves establish that law directly.
Explicit retained masses set the source mass marker, so they need no uniform
premise. Occurrence, map, pay, label, flat choice, and heterogeneous join
derive the remaining leaf obligations through their constructors.
`family_leaves` obtains all local obligations from the computed false family
marker. `dispatched_family_exact` then proves that either source sampler
route equals the full derived family sampler. It does not assume a desired
whole-family probability result.

`RecursiveRuntimeExamples` checks both sampler routes through concrete typed
families with a delayed recursive join. The unweighted result retains four
distinct ranks with probabilities one quarter, even when pairs of ranks have
equal values. Explicit nine-to-one retained masses remain nine-to-one within
both size classes. Further checks cover probe/term phase availability, weight
promotion from a dropped key, and absent-term error precedence.

`BoundedRecursiveDispatch` keeps the finite-wrapper inverse branch separate
from the recursive one. `boundedStatic` installs an empty finite candidate
callback when recursive terms are absent. Therefore public `ranksOf` returns
an empty list and `rankOf` reports `TermNotInLanguage`. Term selection still
reports unavailable terms. With a callback present, the public checked-rank
filter and least-rank theorem remain unchanged. `family_exact` connects this
finite-wrapper behavior to all bounded family term preimages.

The source locations are `Gen/Internal/Join.hs`, `Chain.hs`, `Recursive.hs`,
`Recur.hs`, and `Query.hs`. These are pure field and dispatch adapters. They
do not model evaluation of arbitrary Haskell body functions, source exceptions
outside the shown branches, or a live cache/IO trace.
