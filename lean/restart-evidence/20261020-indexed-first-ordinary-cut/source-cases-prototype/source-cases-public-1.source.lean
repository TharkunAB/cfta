import MicroCFTA.SourceCurrentIndexedFirstOrdinaryCut
import MicroCFTA.SourceCurrentBuildStructuralRowOrigins

/-!
# Source rows at indexed leaf cuts

The same completed source build supplies the selected row or the full
parent row at its indexed first ordinary-child cut.
-/
namespace MicroCFTA.SourceCurrentIndexedLeafSourceRows
open InternedConstructorTemplates
open InternedNestedConstruction (Syntax)
open InternedFreshOrdinaryConstruction (build)
open InternedStoredSubstitution (leaves)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow build_row_origin)
open SourceCurrentIndexedFirstOrdinaryCut (Cut)

/-- An indexed row-bearing leaf derives a source row from the same actual completed call. -/
theorem source_cases [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (raw : Value Symbol Guard) (after : State Symbol Guard)
    (context : Context before inputs) (actual : build expression inputs before = .done raw after)
    (index : Nat) (leaf : Value Symbol Guard) (found : (leaves raw)[index]? = some leaf)
    (row : EdgeValue Symbol Guard) (inside : RowAt leaf row) :
    (RowAt raw row ∧ SourceRow expression inputs before raw after row) ∨
      ∃ parentRow childIndex child inner,
        Cut raw index leaf parentRow childIndex child inner ∧
        SourceRow expression inputs before raw after parentRow := by
  rcases SourceCurrentIndexedFirstOrdinaryCut.split raw index leaf found row inside with
    direct | ⟨parentRow,childIndex,child,inner,cut⟩
  · exact .inl ⟨direct,build_row_origin expression inputs before raw after context actual row direct⟩
  · exact .inr ⟨parentRow,childIndex,child,inner,cut,
      build_row_origin expression inputs before raw after context actual parentRow cut.facts.1⟩

end MicroCFTA.SourceCurrentIndexedLeafSourceRows

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentIndexedLeafSourceRows.source_cases
#print MicroCFTA.SourceCurrentIndexedLeafSourceRows.source_cases
#print axioms MicroCFTA.SourceCurrentIndexedLeafSourceRows.source_cases
