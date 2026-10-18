# Independent review of used Mu row alignment

Review time: 2026-10-18 10:49 CEST. This review changes no production source.
The manifest pins the exact reviewed sources and the selected existing evidence.

## Result and counts

No material issue was found in the nine reviewed public declarations:

- SourceCurrentPublicationNodeRowSurvival: Paired, node, publication. Source SHA-256 9a394d88e00b73676b87eda6aa4849f4c9c91943970bb58a181ab0b76aac1e0a.
- SourceCurrentNativeOriginExposure: Unfold, unfold_origin, keyable, Writer, returned, request. Source SHA-256 20ecd0f0f4ae76264f1cc59f44aee95181c095de0e65f5dc4ee8ff749b8bf046.

The review reuses nine public and two constructed proof pairs. It adds no
production declaration or public pair. A separate evidence-only counterexample
adds one constructed proof pair. No production build or previous proof check
was repeated. The verifier reads the existing full proof and axiom outputs.

## Node callback survival

SourceCurrentPublicationNodeRowSurvival.lean:25 defines Paired. Both RowCall
receipts use the same original source row index. They retain the exact symbol,
full guard, ordered child calls, and both actual buildEdges/makeNode outcomes.
The output row positions need not equal that original index.

The node proof at line 88 uses the actual normalized row membership to find a
raw source row. It obtains ordered child Empty-test equality from paired_rows.
The selected right row is alive. Therefore the corresponding left row is also
alive and survives its actual normalization. The proof retains full fields.
It does not equate the nonempty children or assume their equivalence.

The publication proof at line 146 inverts the same event's actual callbacks.
The root self-filter is an identity on each actual ordinary node result.
The first call is the ordinary callback. The second is the reserved stored-body
callback. Both contexts and their growth come from that publication. Source
children may contain arbitrary nested Mu syntax. There is no BinderFree, Cap,
or unused-local premise. This proves the node row-survival branch. It does not
prove general reconstruction under a common replacement.

## Complete epsilon origins and native writers

SourceCurrentNativeOriginExposure.lean:33 defines Unfold. A supplied complete
Origin of a retained Mu entails an actual successful repaired unfolding. In the
pending branch, the Mu has no epsilon successor and cannot provide that Origin.
The done branch retains the exact full output heap, the literal stored-body
execute under self substitution, Valid of that output heap, and physical Grows.

The remaining Origin is at the ORIGINAL reader heap. It is not moved to the
unfolding's returned heap. Valid alone is not claimed to preserve SemanticHeap,
result residency, or an unchanged heap. The theorem derives one actual unfolding
from the supplied finite Origin; it is not a total unfolding producer for every
resident Mu.

The keyable proof at line 66 uses actual unkeyed-result emptiness. Empty cannot
have a complete row Origin, at any view. Both codecs and the physical query key
then follow. This works for open interned references. It needs no closedness,
Original, BinderFree, publication history, or selected physical nodeEdges row.

Writer at line 92 retains one actual captured owner, request, compiler interval,
protected finish, Good, NodeReady, growth, and ready-cell retention. The Mu Body
is derived from that SAME compiler trace and interval. The returned proof at
line 109 does not identify two independently chosen writer captures. It normalizes
only actual swap/reset forwarding and keeps the exact terminal returned cell.

The request proof at line 138 obtains final History, Good, and growth from the
actual successful native Trace and initial Good/History. The derived physical key
excludes the direct unkeyed arm. A literal Mu result gets its own actual stored
unfolding. A Mu compiler branch also gets its captured Body. Neither receipt
aligns a retained older winner with a prospective optional-binder callback.

## Existing constructed evidence

publication-survival-kernels-direct-3 and its full public-1 pair build an actual
outer used Mu with a nested used Mu child. The source is not BinderFree. The
stored body and ordinary callback are physically different. The selected row has
its exact guard, symbol, arity three, and the produced Paired receipt. This tests
row survival without assuming a child result relation or future callback.

origin-exposure-kernels-6 and its full public-1 pair build distinct closed used
Mu operands with finite leaf and recursive loop alternatives. The actual native
bothMu request returns a retained used Mu. Its nodeEdges list is empty, but its
complete Origin reaches a row through actual repaired unfolding at the final
reader. Initial Good, native History, actual completion, and the checked Trace
are derived from the fixture's own source. The produced Mu Body uses its captured
writer interval. The mathematical width is not a host Int capacity claim.

Both examples are checked integrations. They do not establish a general initial
operand row ancestor, a cross-view origin theorem, or recursive completion.

## Checked boundary for rootErase

The owned evidence theorem UsedMuRootEraseBoundary.nested_binder_boundary uses:

    expression = binder true (union [var 1, node [mk 0 false [var 1]]])
    own = uninterned 0
    inputs = [reference own]

It starts with the actual repaired build from the empty heap. It derives a valid
warm Context at the returned heap. The freshness condition of source_parts holds.
Both the original source and rootErase source return the same raw value at that
same warm heap. rootErase stops at this binder, so rootErase expression = expression.

The raw value is not the bare own reference. It has that literal reference as a
root alternative and also contains own below an ordinary row. Actual root filtering
removes the literal reference while retaining the deep own name. Hence the filtered
value and the rootErase result do not have SameParts. All the other explicit
source_parts premises hold. Removing its BinderFree premise would make it false.
This is a checked boundary of the Lean source transformation. It is not a Haskell
defect, a counterexample to observational reconstruction, or an infinite execution.

Strict attempts 1--3 contain elaboration errors and remain immutable. Attempt 4
checks the complete original theorem with a zero-byte log. Full-public attempt 1
exits zero but reports a proof printer failure. It is unselected. Attempt 5 keeps
that same checked proof private and exposes the exact same public statement by an
alias. The statement-comparison receipt verifies unchanged statement and proof
text. Selected strict-5 has a literal zero-byte log. Full-public-2 prints the whole
public proof and axioms, with all eight settings and no omission or diagnostic.
Only propext, Classical.choice, and Quot.sound occur in the selected reports.
Every owned execution records effective max/high 4294967296 and swap 0, under 5m.

## Stronger design finding and next obligation

The first next obligation is a source-derived comparison for two DISTINCT retained
self replacements. StoredMuBinderChildLineage.Slot at line 25 requires literal
equality of resolved reference values. publication_extend at line 145 extends
both local maps with the SAME literal argument. These laws correctly handle
lexical freshness and captures. They do not directly compare unfolding two distinct
retained Mu results, whose stored bodies substitute their respective self values.

A general binder proof needs an invariant that supports the actual two replacement
values and the actual callback filters. It also needs a causal law for an earlier
keep-first winner. RetainedMuWriterAlignment.Writer and NativeMuPublication.History
already retain the actual earlier publication and callback histories. An ordering
by entry identity would be wrong: an outer binder reserves before an inner binder
can publish. No desired winner law should be supplied as a heap premise.

The relation's view scope must be justified first. OpenObservationSurvival.Related
at line 21 quantifies every depth and EVERY heap view. OpenObservations.Same at
line 33 executes stored Mu unfolds at that selected view. The actual writer laws
supply valid current readers and growth, not arbitrary unavailable or malformed
views. A first useful target is physical Empty agreement plus every finite Same
at one supported common reader for the two actual reconstruction results. If the
induction needs future readers, quantify actual future Keeps readers with derived
support and prove that transport. Neither that future-reader closure nor all-view
Related follows from the current node survival or epsilon exposure theorem.
No claim is made that a particular strengthened Slot relation is sufficient.

StoredNormalizedPlans.Related at line 23 is a pure same-shape plan relation. It
keeps closed captures literal and binds each Mu to a common argument. No general
actual publication-to-that-relation producer exists here. Actual normalization can
also change node/union shape. It cannot replace the missing causal binder proof.

Finally, Same reduces observation depth only when matching ordinary row children.
A stored Mu epsilon step itself need not reduce that depth. A proof must account
for the actual epsilon derivation and source/publication causality as well as
ordinary child induction. General common-replacement alignment, initial operand
row ancestry, active-owner exclusion, fresh-call bounds, and termination remain
separate open obligations. Ordinary query joins also combine full guards from
BOTH operand rows; their initial ancestry must retain that paired derivation.
