# Original cold-cache finite languages

`MergedColdGraphTransport.accepts_stable` proves exact finite-language
transport from an original cold cache to a later cache. It assumes `Facts`
for both caches, `Prepared` for the original cache, actual constructor
`Grows`, issued-reference extension, and `Available` for the original root.
It requires neither `Ready` nor `Prepared` for the later cache.

The raw graph calls stored unfolding from its observation cache at every
Mu. It discards the returned allocation effects. A later call can allocate
a different ordinary identity. The proof compares accepted terms. It does
not assert equal unfolding records or equal successor lists.

`MergedColdInterpretation` proves the actual `makeNode` and `makeUnion`
language equations for any interpretation that satisfies the ordinary
constructor laws. Recursive values can have arbitrary languages.
`MergedColdBuildLanguage.build_plan` applies those equations to the actual
binder-free lexical executor. It derives the result language from the
source plan and the lexical input languages. Cache lookup, canonical
ordering, duplicate removal, and dead-edge removal remain in the proof.

`MergedColdGraphApprox` bounds the number of Mu exposures on each run path.
Constructor steps and explicit unions keep the same bound. Mu exposure
reduces it. The module proves that these bounded runs have exactly the
finite raw-graph language when the bound is existentially quantified.
This bound is a proof device. It does not replace the source worker.

`MergedColdGraphTransport.approx_stable` inducts on the exposure bound and
ordinary record size. Preparation makes each stored unfolding binder-free.
Its original lexical leaves remain available after cache growth. The plan
language theorem then equates both executions at the smaller exposure
bound, even if their fresh ordinary identities differ.

`MergedColdMergeOriginalLanguage.source_execute_complete` composes this
transport with the complete source-grouped cold worker. It derives a
stable comparison bound and includes every term accepted in the original
cold cache in the actual returned result language. The inclusion also
holds in every later cold extension. `source_successful_sound` gives the
same guarantee for every successful pair of source worker fuel bounds.
The source grouping and recursive coverage premises are discharged by the
existing worker proofs. Guard soundness and the Top guard interpretation
remain explicit. Merge can widen a language, so the result claim is
inclusion, while transport of an unchanged original record is equality.

`MergedExposureOriginalLanguage.nodeEdges_exact` equates the original cold
root language with the returned edges interpreted in the reader's actual
final cache. `MergedComparisonOriginalLanguage.check_sound` gives inclusion
between both original operand languages before a true comparison starts.
`MergedSelectionOriginalLanguage.select_exact` equates the actual retained
list language with the original input union language before any effects.
These bridges use the proved transport theorem and the completed worker
semantics. They require no new callback or warmup premise.

The pinned Lean 4.34.1 build checks all five modules through
`MergedColdMergeOriginalLanguage`. The isolated theorem-dependency audit
allows only `propext`, `Classical.choice`, and `Quot.sound`. The modules do
not change Haskell source. The source adapters and initial `Facts`,
`Prepared`, and `Available` obligations retain their documented scope.
