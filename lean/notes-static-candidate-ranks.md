# Static outcome discovery after integer filling

`StaticCandidateRanks` models the finite `outcomeRanks` callbacks in
`Gen.Internal.Static`. It covers pure, hole, indexed source, map, pay,
application, binary frequency choice, and flexible label constructors.
The executable selector retains the private term and its source rank.
Its soundness and completeness follow from the constructor relation.
`select_total` proves that each rank below the cardinality selects a term.
Source term validity and rank bounds also follow from that relation.

`candidates` follows the source callbacks for all three term views.
Application uses the final spine argument and the function spine prefix.
Choice preserves the branch index in whole and spine views. It searches
both branches in labelled views and retains their rank offsets.
Labels pass their children to the inner labelled-view callback.
The model omits `CheckedRank` flags because `pointsStatic` ignores them.

`candidate_complete` proves that every selected original rank remains a
candidate after integer filling. It derives this result for each source
constructor. It does not assume a complete original candidate callback.
The proof uses the typed projection laws in `IntegerTermViews`.
It permits repeated terms and repeated views from different outcomes.

`pointCandidates` then executes the source candidate scan. It selects each
original outcome, reads and ranks the integer point, checks the final
filled view, and combines the original and point ranks.
`pointCandidates_exact` proves exact membership in this combined rank list.
Its witnesses are successful executable original selections and valid
point ranks whose filled views equal the requested view.
`pointCandidates_sound` also proves the final product-cardinality bound.

Completeness requires a successful lattice-point construction, a literal
reader inverse, the required hole count, and local label compatibility.
`integer_label_compatible` obtains the label condition from successful
`IntegerLabelCodec.exactLabel` specialization and `exactLabel_matches`.
This condition concerns the primitive flexible-label matcher only.
It does not assume candidate coverage. Specialization failures remain
outside this total filling model. The theorem states its success premise
for every point list supplied to the specialization function.

This module does not cover arbitrary enumerated or imported static
sources, n-way or keyed joins, or recursive callbacks. Binary choice is
the two-branch source case. Errors project to absent outcomes; the model
does not retain the source error vocabulary. The complete Haskell record
construction and runtime execution remain source representation interfaces.
No counterexample was found in the covered constructors. No Haskell code
changed for this proof.

Validation: `lake build MicroCFTA.StaticCandidateRanks` succeeds with the
pinned toolchain. The principal theorem audit reports only standard Lean
axioms. The module has no added axioms or incomplete proofs.
