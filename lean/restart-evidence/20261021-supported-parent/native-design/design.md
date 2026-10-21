# Nested publication position design and prior-art correction

Written 2026-10-21 02:49 CEST. Source-only review. Zero Lean commands and zero new proof pairs. Every proposed new theorem below is unchecked. The separate BinderFree theorem c6b0fa14 remains frozen and checked; this package changes none of its files.

## Recommendation: use the existing exact unused-return law first

A new full nested position heap is not required for the immediate native cleanup consumer. The existing theorem SourceCurrentNativeNormalizedComparisonExecution.history_unused, lines417–424, already proves:

```lean
(history : SourceCurrentNativeMuPublication.History empty state)
(present : state.nodeRecords key = some (.mu entry body depth ordinary))
(unused : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false)
-- conclusion:
InternedNestedConstruction.finish true (.mu entry body depth ordinary) =
  SourceCurrentNativeCallbackErasure.eraseSelf
    (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) ordinary
```

The history induction derives its internal MuLaw from actual source publication. It visits the actual Depth, ordinary and body histories before each candidate. The syntax comparison and history proof are joint. The law is not assumed for new candidates. complete retains the SAME earlier winner's law on a warm hit. This source already covers arbitrary nested syntax. closed_unused, line426, derives the causal history from actual empty source build, including stopping states without a successful final result premise.

SourceCurrentNativePublicationTrace.source_unused, lines185–202, is the concrete native-prefix producer. Its inputs are the actual physically admitted checked Trace, exact initial heap=(build source [] empty).state, the SAME reached full Mu record and unused flag. It derives the exact equality above. It does not require Good, a supplied future return, an internal native memo History or a desired callback comparison. reached_unused, line171, supports an explicit initial semantic heap and actual prior causal publication History. source_trace, line155, derives semantic state and causal history for the SAME prefix. trace/execute, lines106/122, cover actual yielded prefixes and all bounded outcomes, respectively. No Grows-to-History inference occurs.

The pure eraseSelf operation in SourceCurrentNativeCallbackErasure line26 changes a value only when it is the literal reference to its argument. Both that reference and Empty have no PositiveAt. Therefore the following local pure lemma follows by source case analysis:

```lean
∀ name value path,
  PositiveAt (SourceCurrentNativeCallbackErasure.eraseSelf name value) path ↔
    PositiveAt value path
```

Composing it with source_unused derives the SAME-path native UNUSED RETURN equivalence, without a BinderFree restriction. This is the smallest useful next implementation if that consumer is still missing. It is not a new desired-position premise: the actual source-started Trace derives the history and earlier-writer law.

## Strongest small native endpoint

One can remove the supplied unused flag from the result-facing theorem. Propose one public source-started prefix endpoint with the same actual Trace/initial equality/full-cell premises as source_unused:

```lean
PositiveAt (InternedNestedConstruction.finish true (.mu entry body depth ordinary)) path ↔
  (InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false ∧
    PositiveAt ordinary path)
```

Derive source_trace ONCE to obtain the SAME reached semantic heap and causal history. Split the actual usesLocal Boolean. For false, apply history_unused to the SAME selected full cell and then the pure eraseSelf lemma. For true, the reached SemanticHeap includes DepthHeap.Correct for that same cell. SourceCurrentNativeNormalizedComparison.retained_of_used, line317, then makes finish return the SAME opaque Mu. PositiveAt of Mu is impossible. The equation therefore covers every smart finish, both used and unused, while retaining the exact ordinary probe of the selected writer.

For an actual warm request whose supplied probe values must be aligned with the stored values, use InternedProfileHeap.stored_probes, line60, under its actual physical Facts and Available probes. That lemma derives equality of the complete depth and ordinary values, not just their references. It adds no body law. These alignments must stay at the SAME heap and selected cell. An operation returning a body in the no-pair maybeMu bypass is already an identity case and does not need a stored writer.

A further Boolean split on smart extends this to finish smart: its positive positions are exactly smart=true together with usesLocal=false and the SAME ordinary position. Raw finish retains the opaque Mu. This extension needs no additional physical premise.

This endpoint advances the actual native support proof: a newly visible nonplain ordinary row after unused smart cleanup is present at exactly the same child-index path in the retained writer's ordinary probe. It does not yet connect that probe path to an original user-program child or prove a global call bound.

## Full raw body-to-ordinary law remains a distinct stronger target

The requested all-publication law is stronger:

```lean
PositionCorrect entry body depth ordinary :=
  ∀ path, PositiveAt body path ↔ PositiveAt ordinary path
```

history_unused does not establish it for a USED payload. In that branch finish is opaque, so it cannot observe the raw body's positive paths. Likewise SourceCurrentNestedSourceInertBinder.publication_eq, line143, derives literal body=ordinary only under its static Inert support restriction; Inert excludes all contribution from the own slot and is stronger than no deep local use. Neither theorem should be relabeled as the unrestricted full law.

The complete source-grounded target would be the expanded heap statement at every stopping outcome of actual build source [] empty. No completed outer return or Scoped source premise is needed. A warm preservation endpoint would take the initial positional heap and genuine initial Context, then derive the actual stopping heap. The empty-source corollary must discharge the initial heap vacuously. A candidate's current body/probe relation cannot be a caller premise.

## Minimal simultaneous proof if the stronger law is still required

Use private domain-specific observation data only. Pair the existing InternedDepthSemantics.Shape with a path predicate of type List Nat→Prop. Decode each captured value as (InternedRecordDepthShape.shape value, fun path=>PositiveAt value path). Do not replace Mu by its body: captured and retained Mu predicates are false because PositiveAt is opaque at Mu.

The pure source evaluator has these cases:

- Empty and literal references have the false path predicate.
- A union combines member predicates by disjunction and adds no child index.
- An ordinary row tests the existing child shapes for Empty. A dead row contributes false. A live row contributes its nonplain full guard at[] and its selected child predicate at index::suffix. Retain actual natural lookup in the ordered evaluated child list.
- A raw binder or a smart binder with a deep local contributes false. An unused smart binder keeps the body predicate. Use the existing hasLocal Boolean of the distinguished symbolic local. Do not infer local use from the path predicate.

The evaluator's map on names changes only the structural Shape; it leaves the path predicate unchanged. As in GuardSemantics.evaluate_map/evaluate_supplied, this yields identical predictions for the ordinary and reserved callback names. It permits external aliases and arbitrary fixed captures. It does not require reference-name injectivity. The actual source root filter preserves PositiveAt; the checked BinderFree component already contains the required physical filter/union proof, but its private names must not be imported.

The simultaneous actual invariant is:

1. Every stored Mu at the actual stopping heap satisfies PositionCorrect for its literal complete payload.
2. Every successful actual build return has exactly the private evaluator's path predicate at each path. Pair it with the existing structural Shape observation, or derive that observation independently from RecordDepthExecution.build_depth at the SAME initial Context/DepthHeap.
3. Ordered actual child returns retain this observation at each natural index; actual edge returns retain the full original guard and those exact ordered children.

The mutual proof follows GuardExecution.build_profile/buildMany_profile/buildEdges_profile. It derives intermediate support from actual earlier results. Ordinary constructors use actual coherent complete row readback, matching child emptiness and canonical surviving rows. Union readback handles ordinary merges and exact cached member lists. It must not infer actual full member equality across two different heaps.

In the binder branch, the two actual probe returns and a reserved body return supply their own predictions by the induction hypothesis. Name-map invariance gives body-to-ordinary PositionCorrect for a fresh candidate. The heap is threaded through Depth, ordinary, reservation and body before publication. A warm hit reads the earlier stored payload law from the derived current heap, using stored_probes to align exact probes. No earlier event or history is reconstructed backwards from growth.

Reuse SourceCurrentNativeNormalizedComparison.probes_use, line257, to derive the actual usesLocal depth ordinary from the SAME two callback equations and initial Context/DepthHeap. Reuse retained_of_used for the used branch. For unused readback, either apply the existing actual-history equality when a history from empty has already been derived, or use PositionCorrect plus the exact cleanup/depth cases. The former route gives a stronger literal result for the immediate native endpoint and avoids implementing this large theorem merely for that endpoint.

A new public predicate or generic proof engine is unnecessary. The full-source public closed_heap theorem can expand the stored-record quantifiers directly, with all observation types private. If a real native consumer later needs warm preservation from an initially derived positional heap, expose that actual build preservation theorem rather than an assumed callback relation.

A realistic implementation estimate for the unrestricted law is about600–850 new lines: name-map/evaluator lemmas, actual physical path normalization, smart readback and a mutual actual syntax induction. This estimate includes copying necessary private physical lemmas additively from the frozen BinderFree component; those private names cannot be imported. It is not justified for the immediate unused-return handoff, which should require roughly30–70 lines and no new generic observation framework.

## Counterexample search and boundaries

No actual source-built counterexample to the unrestricted raw body/probe law was found or proved in this zero-job review. The model's literal callbacks, repaired fresh ordinary level, exact normalization and decoded nested cleanup are consistent with the simultaneous route above. This is a design assessment, not a new proof.

Existing ProducerPathBoundary explicitly shows an actual nested writer can retain a capture even after a dead enclosing row makes the original producer result Empty. It rules out transferring nested liveness through a mere Reached path, not the fixed-event body/probe position claim. FreshOrdinaryCostReplay checks an old probe-cost example after repaired ordinary-name selection; it does not refute the position claim. The known artificial-writer examples and the root's new arbitrary-Good counterexample do not have the required actual source publication history.

The immediate exact cleanup endpoint is established in existing source for nested syntax and warm winners. The stronger used raw-body position law, full residual Mu observation ancestry, original source child ancestry, global native renewal rank, termination and Haskell refinement remain separate. The two History types must stay distinct: NativePublicationTrace produces causal MuPublication.History, not native memo History.
