# Independent guarded language and actual stored plans

Updated: 2026-10-14 16:24 CEST. Proof checkpoints: `4457307a`, `e46d3f9e`, `e1baab1e`.

## Independent meaning

`InternedGuardedLanguage.meaning` interprets complete actual stored records.
A reference reads a language from an environment indexed by `Reference`.
A node retains each actual source symbol, full guard, and ordered child list.
A union denotes its member languages. A Mu denotes the least language of
its actual body at its own interned name. This definition ignores probe
metadata and cache allocation. It does not call the cold reader.

`meaning_mono` proves positivity. `mu_unfold` proves the least-language body
equation. `forest_all` identifies the ordered forest with `Language.All₂`.
`laws` derives the ordinary constructor interface for this interpretation.
The guards are arbitrary predicates on complete finite terms.

`InternedGuardedSyntax.evaluate` gives the complete lexical source syntax
its independent guarded meaning. Variables read their lexical positions.
Both binder forms denote the least language of their body with one new local.
`evaluate_mono` and `binder_unfold` prove positivity and unfolding.

## Actual metadata and normalization

`InternedGuardedLanguageSupport.meaning_free` follows coherent available
records. Actual cached free names contain every ambient reference that
the independent meaning can read. `closed_meaning` therefore makes a closed
captured record independent of the ambient environment.

`InternedGuardedConstructors.makeNode_exact` and `makeUnion_exact` apply the
proved actual normalization laws to this independent meaning. They retain
complete guards and child order. `unused_mu`, `self_mu`, `cleanup_exact`,
and `finish_exact` prove the actual smart cleanup and both finish paths.

`InternedGuardedSelfFilter.filter_closed` follows the actual callback root
filter and its union reconstruction. The original and filtered bodies have
the same closed candidate languages. `filter_least` and `filter_mu` derive
the same least language. No preparation, productivity, or literal identity
reconstruction premise is used.

## Actual stored compiler

`InternedGuardedStoredPlan.encode_language` interprets the exact
`InternedStoredSubstitution.encode` plan. Coherent canonical slot lookup
retains each closed captured record. Local names read the nearest lexical
slot. Open Mu records compile to lexical least-language binders.
The theorem covers arbitrary nested records and arbitrary lexical languages.
It keeps full symbols, guards, and ordered forests.

`execute_plan_language` specializes the theorem to the actual simultaneous
replacement map. Each original free name gets the ambient meaning of its
actual optional replacement. Closed captured records remain constants.
`unfold_plan_language` proves that the exact outer-Mu unfolding plan has
the independent least language of that Mu.

## Complete source analysis support

`InternedGuardedAbstractSupport.Related` combines root-language bounds with
free-name support. A pure root profile bounds its language by its literal
root alternatives. A smart binder lowers that bound by a closed candidate
argument. Both binder forms retain external-name support.

`InternedGuardedSyntaxSupport.evaluate_related` proves both properties for
complete lexical syntax. A filtered edge has an empty child profile. The
child's root bound proves that no finite accepted term can use that edge.
All retained guards and ordered forests remain in the interpretation.

`InternedGuardedProfileSupport.profile_upper` derives root bounds directly
from actual stored profiles. `values_inputs` combines these bounds with
coherent cached free-name support. `body_captures` and `body_bind_fresh`
show that only surviving symbolic captures need fresh local names.
Unused supplied inputs can contain the chosen ordinary sentinel. Do not
replace the proved capture-freshness condition by all-input freshness.
`InternedGuardedProbeHeap.ordinary_fresh_captures` follows the actual chooser.
`next_fresh_captures` follows actual issued-name bounds.

## Actual source execution

`InternedGuardedProbeHeap.Correct` equates each actual stored Mu's independent
language with the least language of its exact ordinary probe. The probe name
is `.uninterned (ordinaryLevel depth)`. Guards and ambient environments are
universally quantified. `Heap` requires this law for all complete Mu records.

`InternedGuardedRequest.request_heap` derives the candidate invariant from
recursive callback least languages. A completed canonical hit retains its
existing invariant. `request_language` uses exact coherent requested probes,
actual cleanup, and the completed stored record. No discarded candidate
replaces a canonical hit.

`InternedGuardedExecution.build_language` proves execution correspondence and
heap preservation in one source induction. It follows ordered children and
edges, both probes, root-self normalization, fresh completion, and canonical
readback. Pending results retain the heap. `closed_heap` derives the invariant
from empty caches. `closed_language` identifies every completed closed source
result with independent lexical meaning. No callback or execution contract
is assumed.

`InternedGuardedStoredExecution.execute_checked` composes that source theorem
with exact stored compilation. It proves the actual capture-free simultaneous
replacement language and preserves the heap. `unfold_checked` proves that
actual repaired outer-Mu unfolding retains independent language for arbitrary
available records. It uses no preparation or literal reconstruction premise.

## Actual cold traversal

`MergedFreshOrdinaryGuardedEffects.collect_heap` and `nodeEdges_heap` retain
the independent probe-language heap through every bounded actual cold read.
Exhausted bounds retain the heap. `SourceFreshOrdinaryColdSharedRows.Trace.guarded_heap`
follows each actual read and carries the invariant to the exact final cache.
`cold_finite_guarded` composes this law with existing finite traversal.
`constructed_cold_finite_guarded` derives every initial premise from actual
completed closed construction. Both depth and independent-language probe heaps
hold in the resulting finite shared table.

## Next proof

Connect the actual final repaired graph and finite cold table to independent
meaning. Then derive physical `ProductReadback.members`, `.rejected`, and
`product_exact`. Propagate the new semantic heap through native intersection effects
where those paths construct binders. Cold/shared propagation is proved. Their older depth/free/profile heaps
remain separate proved invariants.

`MergedFreshOrdinaryGraph` uses actual repaired unfolding but fixes one cache.
Keep availability, replay, and cache growth explicit when following its
successors. Graph acceptance is least finite-run acceptance. Equal unfolding
equations alone do not prove completeness through unguarded epsilon cycles.
The existing final-cache graph/table theorem and new execution theorem are
component results. Their full independent-language transport remains open.
The raw unused-binder identity counterexample still applies.

## Validation

Lean 4.34.1 passes 1,411 aggregate jobs and 43,431 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-guarded-cold-heap-20261014-audit.log`.
No production Haskell source changed. Existing Nix and formatter checks remain
applicable. The earlier proofs, counterexamples, and marked drafts remain.

All 1,769 files from the previous local snapshot remain. The current Lean
tree has 1,771 files. Only audit imports, coverage ledgers, and this note
changed among earlier files. All earlier proof bytes and marked drafts
are unchanged. Snapshot:
`/tmp/mcfta-guarded-cold-heap-checkpoint-20261014-1624/`.
