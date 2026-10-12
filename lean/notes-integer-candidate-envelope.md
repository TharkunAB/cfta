# Integer candidate-oracle completeness

The source `integerCandidates` obtains a one-variable point table. It then
reads rank zero and the last rank. It offers every integer between those
values to the complete witness checker. The interval can include integers
that do not satisfy the formula.

`IntegerCandidateEnvelope` proves that this candidate interval cannot omit
an integer solution. It does not assume that the lattice decoder is sorted.
`one_rank` derives the source rank equation from the actual recursive ranker.
`core_rank_monotone` derives coordinate monotonicity from the compiled
cumulative polynomials. `one_decode_strict` then proves strict value order
for increasing ranks of every successful current full-syntax point table.

`integerAt_shape` proves that each endpoint decode has exactly one integer.
The source partial singleton reader therefore has no malformed tuple at
these ranks. `zero_count` connects the signed stored count to the natural
rank-domain check. `candidates_complete` proves that every solution lies
between the two actual decoded endpoints, including nonconvex domains.
`integerCandidates_error` retains unsuccessful lattice construction.
Unsupported and unbounded domains are not treated as empty languages.

`filtered_exact` composes the complete interval with an exact complete-term
witness check. Its checker law is explicit; an incomplete solver may return
Unknown instead of that Boolean decision. This theorem does not prove the
entire witness evaluator or make an arbitrary callback exact. It also does
not treat the overapproximating candidate interval as an accepted language.

The interval can be much larger than the valid point set. This is a
completeness result for the diagnostic candidate oracle, not an efficiency
claim for enumerating wide sparse intervals. The counted production decoder
uses its own direct point index.

The guard-to-integerDomain extraction and complete witness construction are
separate adapters. The source retry wrapper has no alternate coordinate
order for a one-variable table. Host tuple storage and integer range
construction remain representation interfaces.

Validation: the pinned `lake build MicroCFTA.IntegerCandidateEnvelope`
succeeds. No Haskell source changed.
