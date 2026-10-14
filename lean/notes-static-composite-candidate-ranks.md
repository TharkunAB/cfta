# Composite static candidate callbacks

Name examples use the current `__cfta_` prefix from PR #129.
Earlier saved log transcripts use the historical `__microcfta_` prefix.

`StaticCompositeCandidateRanks` extends the source callback model to
`Join.joinNBucketStatic`, `Chain.chainRanks`, and arbitrary-length
`Static.frequencyStatic` choices. Its component terms and ranks come from
`StaticCandidateRanks.Source` and its constructor-derived `Selected` relation.

`chainCandidates` reads each argument under its `ArgKeyed` wrapper.
It uses the cardinality of the remaining chain as the next radix.
`joinCandidates` reads the operation under `CenterKeyed` and combines its
rank with the chain rank. Whole and spine views retain `JoinN`; labelled
views contain its children. The filling lemmas derive preservation of the
private keys, coordinate suffixes, and argument order. `join_complete`
then proves candidate inclusion without assuming a whole-join coverage law.
`chain_rank_bound` derives the product bound from selected component ranks.

`frequencyCandidates` executes the cumulative branch traversal. It adds
each preceding branch cardinality to the rank offset and increments the
private choice index. `frequency_complete` proves the exact cumulative
offset for any selected branch, including a branch after empty alternatives.
The theorem has no fixed limit on the number of alternatives.

These callbacks erase `CheckedRank` flags only because `pointsStatic`
discards the incoming flags and checks its final rewritten view.
The module does not assert checked-flag soundness for `Query.ranksOf`.
In particular, the source join also checks `joinKeysMatch`; this module
proves preservation of constructed keys but does not model that Boolean
check or unchecked user-supplied key terms.

`Inert` states local closed-term conditions: no placeholder and no user
label that changes under the selected specialization function.
`fill_inert` derives both unchanged terms and unchanged coordinate suffixes.
`enumerated_complete` then proves exact stored-outcome candidate inclusion.
`opaque_complete` covers the imported source's singleton `leafRanks`
adapter for an opaque user root. It retains the underlying term inverse's
rank premise; it does not prove the imported automaton compiler again.

The closedness condition is necessary. `open_enumerated_counterexample`
checks that an enumerated placeholder cannot recognize its filled integer
term. This is a counterexample to an unrestricted internal callback law,
not a reproduced defect in a valid public generator. The source open
compiler uses structural callbacks for open integer regions. It obtains
enumerated and imported components through its closed-region path.
An imported formula that uses `__cfta_integer_*` can collide with
filling, but `Refinement.Expression.variable` explicitly reserves the
`__cfta_` prefix for library names.

The module proves a join or frequency adapter over the earlier finite
source fragment. It does not introduce one recursive syntax that nests
all new composite constructors. It also does not derive the complete
compiler's closed-region invariant or callback record wiring.
These remain explicit composition and representation boundaries.
The source sweep found no valid public counterexample in these callbacks.
It required no Haskell changes or Cabal runs.

Validation: `lake build MicroCFTA.StaticCompositeCandidateRanks` succeeds
with the pinned toolchain. The principal theorem audit reports only standard
Lean axioms. The module has no added axioms or incomplete proofs.
