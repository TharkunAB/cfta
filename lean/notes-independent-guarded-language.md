# Independent guarded language and actual stored plans

Updated: 2026-10-14 17:28 CEST. Latest proof: `9288ec6d`. Earlier support/execution checkpoints remain.

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

## Soundness through growing caches and final tables

`MergedFreshOrdinaryGuardedSoundness.collect_sound` follows actual ordered
cold effects. A returned edge's independent language belongs to one original
root. Each Mu step uses actual unfolding language equality. Cache growth does
not define the language. `nodeEdges_sound` covers direct reads and canonical
closure output. Skipping a visited root is sound for this inclusion.

`SourceFreshOrdinaryColdGuardedSoundness.row_sound` uses actual canonical row
replay. `language_sound` follows finite terms and declared child rows.
`graph_sound`, `trace_graph_sound`, and `trace_table_sound` identify soundness
for the actual final repaired graph and ascending finite table. These laws
prove inclusion into independent root meaning. They do not prove completeness.

## Native binders, heaps, and output tables

`SourceRecursiveIntersectionGuardedEffects.optionalBinder_checked` proves
actual optional-binder least language at the repeated-pair reference. It
also covers the unused branch and all heap outcomes. The proof composes the
exact lexical compilation with actual source execution.

`SourceRecursiveIntersectionNative.Bounds.guarded_heaps` follows ordinary
work, domain effects, reads, optional binders, checked memo hits, nested source
bodies, completion frames, and continuations. `NativeColdGuarded.cold_node_table_sound`
and `constructed_node_table_sound` derive finite stable native tables that
are sound for the independent language of the returned physical value.
The existing complete-cache, closed Original input, and checked-word scope
remains. This is not yet the intersection language of the two inputs.

## Agreement with original finite input derivations

`SourceRecursiveIntersectionGuardedInput.original_meaning` proves that
Original payload syntax has the same independent stored and copied lexical
meaning. The interned reference environment map commutes with actual binders.
`input_exact` derives exact finite tagged input derivations for every closed
available original record. The existing input specification and the new
stored interpretation therefore agree without a copy-language contract.

## Next proof

`e8f06e62` defines complete stored languages at each Mu-unfolding budget.
Actual ordinary normalization preserves each budget. Cleanup retains accepted
terms without increasing the bound. Actual root-self filtering preserves the
budgeted least Mu language. `19467e4a` proves exact actual finite input
derivations at each bound for closed available Original records. Erasing the
bound recovers independent stored meaning. This is separate from public term
rank. See [unfolding budgets](notes-unfolding-budget-language.md).

`9288ec6d` proves exact raw budgets for arbitrary nested stored compilation
and simultaneous-substitution plans. Each accepted Mu has its actual compiled
outer-unfolding plan at a strictly smaller bound. This law is before source
execution. Exact smart costs need the existing deep-local cleanup decision.
Reuse `InternedDepthSemantics.Shape` and `InternedRecordDepth*`; actual source
and canonical-hit budget transport remain unproved.

Prove completeness of the final repaired graph and finite table for independent
meaning. Then derive physical `ProductReadback.members`, `.rejected`, and
`product_exact`. Soundness and native/cold/shared semantic heap propagation
are proved. Do not repeat them.

`MergedFreshOrdinaryGraph` uses actual repaired unfolding but fixes one cache.
Keep availability, replay, and cache growth explicit. Graph acceptance is
least finite-run acceptance. Equal unfolding equations alone do not prove
completeness through unguarded epsilon cycles. The new `input_exact` gives
finite input derivations for Original records. Exact budget correspondence
now strengthens this law. Any rank transport through
actual reconstruction and canonical hits must be derived before it is used.
The raw unused-binder identity counterexample still applies.

## Validation

Lean 4.34.1 passes 1,430 aggregate jobs and 43,598 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-budget-stored-plan-20261014-audit.log`.
No production Haskell source changed. Existing Nix and formatter checks remain
applicable. The earlier proofs, counterexamples, and marked drafts remain.

All 1,787 files from the previous local snapshot remain. The current Lean
tree has 1,789 files. Only audit imports, coverage ledgers, and the two current
component notes changed among earlier files. All earlier proof bytes and marked drafts
are unchanged. Snapshot:
`/tmp/mcfta-budget-stored-plan-checkpoint-20261014-1728/`.
