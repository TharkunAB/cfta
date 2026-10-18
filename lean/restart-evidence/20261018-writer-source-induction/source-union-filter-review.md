# Actual source union and root filter induction

Reviewed at 2026-10-18T09:43:03.386545+00:00.

Production: `lean/MicroCFTA/SourceCurrentSourceUnionFilterInduction.lean`.
SHA-256: `fd8ed03affeb81448f9d8d143e084e8198b9d0538913166495823f6afb298fef`.
Public declaration: `SourceCurrentSourceUnionFilterInduction.union_filtered`.

## Derived result

The two actual `build (.union expressions)` calls can have arbitrary entry
and return heaps. Each starts with its own original lexical Context.
The theorem derives raw `RootMatch`, exact bare-self parity, and `RootMatch`
of both literal `withoutSelfReference` results at the actual raw return heaps.
It does not require warm source calls or a common heap.

Actual buildMany inversion supplies the member calls and their real entry
Contexts. Context.build transports each original lexical context across the
actual completed earlier source call. All2 pairs both outputs by the same
source member. The public child hypothesis is restricted by an exact source
index lookup and a strict syntax-size witness. The proof derives that witness
from the actual member occurrence. It invokes the hypothesis at the actual
pair of entry and return heaps. No child graph or desired parent result is
supplied.

The proof derives each member's live alias facts from the initial union
alias facts. It uses exact source support inclusion and retains the Depth
anchor. It does not assume global freshness or injective lexical labels.
The public selfTests premise concerns only initial live source support.
The referenceLocal premise describes the supplied reference relation's
own-name tests. Neither premise describes desired returned root parts.

The actual makeUnion calls use their computed member values and their own
intermediate Normal heaps. union_ordered retains both directions of literal
atoms and full ordinary rows. Complete symbols, complete guards, and ordered
child relations remain in RootMatch. The raw bare-self parity follows from
OutputTags.bare and the initial source tests. The actual filter theorem then
accounts for bare self remaining unchanged while union self is removed.
The theorem derives the whole-parent RootMatch; it does not assume it.

## Induction boundary

The child relation `values` is arbitrary. It can describe a fixed-reader
finite observation relation or actual child-call comparisons, but this module
does not produce a stored-execution comparison from RootMatch. Generic
ReaderReplacementSlots.Paired is not a premise. That predicate alone does
not imply raw reference-name alias tests. An unused Paired premise would
not justify those tests.

Nested Mu syntax is allowed in source members. Its corresponding strict
member induction obligation remains to be proved elsewhere. RootMatch's
AtomMatch compares Mu only with Mu. It cannot close a mixed Mu versus
ordinary or reference smart-erasure case. Earlier selected-writer induction
and stored reconstruction alignment remain separate.

The proof never transports RootMatch or a finite reader relation along heap
growth. It preserves the relation at its supplied arguments. This avoids the
later-reader invocation in the older all-view PairedUnion proof. No new
counterexample to a stronger warm-closure theorem is asserted here.
No BinderFree, noDeep, finite Cap, or completed recursive callback law is added.

## Checks

Selected strict `source-union-filter-direct-2`: exit 0, raw log exactly 0 bytes.
Selected canonical `source-union-filter-canonical-1`: exit 0.
Selected imported full probe `source-union-filter-public-1`: one public pair.
All eight print/linter options, #check @, full #print, and #print axioms are
explicit. No omission, printer failure, warning, error, or sorryAx occurs.
Only standard propext, Classical.choice, and Quot.sound axioms occur.

Every selected worker records effective memory.max=4294967296,
memory.high=4294967296, and memory.swap.max=0 before Lean starts.
The wrapper uses pinned Lean 4.34.1, a five-minute timeout, and owned peaks.
Direct-1 is retained. Its one elaboration error was a rewritten equality in
union_parts: cases had already changed the target's buildMany equation to
reflexivity. Direct-2 corrected that proof argument only.
No separate constructed scenario is counted in this bounded component.
No old source or old evidence was changed. Shared root artifacts are excluded.
