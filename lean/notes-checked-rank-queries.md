# Public rank queries and checked-symbol flags

`CheckedRankQueries` ports `Query.ranksOf` and `Query.rankOf`. A candidate
contains a signed rank and the source checked-symbol flag. A true flag
bypasses term replay. A false flag makes the query decode that rank and
compare the complete requested term. Decode errors fail that comparison.

`candidates` retains finite and recursive construction errors. It
separates an unavailable recursive term index from an opaque generator.
`source_error` proves that these construction failures do not become
`TermNotInLanguage`. There is no negative-rank input to this inverse query;
the candidates themselves carry signed ranks.

`keep_exact` and `retained_exact` prove exact membership of the filtered
result. `retained_sublist` preserves order and cannot introduce duplicates.
`rankOf_exact` proves that the public inverse returns the least matching rank
when the callback supplies ascending ranks. `rankOf_rejected` proves exact
nonmembership when candidate discovery is complete.

Three local callback obligations remain explicit: a true checked flag must
imply exact successful replay; every matching rank must be offered; and
candidate ranks must be ascending for the least-rank claim. The proofs
establish the query filter. `StaticCheckedRanks` and `StaticRankQueryExact`
now derive these producer obligations for the finite constructor algebra,
with only local label self-matching required. Existing
candidate-discovery modules erase flags only because `pointsStatic` ignores
them and performs its own final comparison. They do not establish certificates for recursive or composite producers.

`unchecked_contract_necessary` supplies an invalid callback countermodel:
a fabricated true flag admits a negative rank with the wrong term. This is
not a reproduced public-library defect. It records why checked-flag producer
soundness cannot be replaced by candidate completeness alone.

Validation: the pinned `lake build MicroCFTA.CheckedRankQueries` succeeds.
No Haskell source changed.
