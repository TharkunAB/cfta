import MicroCFTA.SourceCurrentBuildStructuralRowOrigins

/-!
# Open ordinary leaves from actual source child calls

An indexed leaf retains its canonical row, ordered child, and inner leaf
position. The same row retains its original source index and actual child
call. Source positions and canonical positions remain separate.
-/
namespace MicroCFTA.SourceCurrentOpenOrdinaryLeafSourceCalls
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open InternedStoredSubstitution (leaves manyLeaves edgeLeaves)
open InternedEdgeResidency (nodeEdges)

private theorem flat_lookup (f : α → List β) (values : List α) (index : Nat) (value : β)
    (found : (values.flatMap f)[index]? = some value) :
    ∃ outer selected inner,
      values[outer]? = some selected ∧ (f selected)[inner]? = some value ∧
      index = ((values.take outer).flatMap f).length + inner := by
  induction values generalizing index with
  | nil => simp only [List.flatMap_nil,List.getElem?_nil] at found; cases found
  | cons first rest ih =>
      simp only [List.flatMap_cons] at found
      by_cases short : index < (f first).length
      · rw [List.getElem?_append_left short] at found
        exact ⟨0,first,index,rfl,found,by simp only [List.take_zero,List.flatMap_nil,List.length_nil,Nat.zero_add]⟩
      · have long : (f first).length ≤ index := by omega
        rw [List.getElem?_append_right long] at found
        obtain ⟨outer,selected,inner,source,inside,offset⟩ := ih (index - (f first).length) found
        refine ⟨outer + 1,selected,inner,source,inside,?_⟩
        simp only [List.take_succ_cons,List.flatMap_cons,List.length_append]
        omega

private theorem many_flat (values : List (Value Symbol Guard)) :
    manyLeaves values = values.flatMap leaves := by
  induction values with
  | nil => simp only [manyLeaves,List.flatMap_nil]
  | cons first rest ih => simp only [manyLeaves,List.flatMap_cons,ih]

private theorem edges_flat (rows : List (EdgeValue Symbol Guard)) :
    edgeLeaves rows = rows.flatMap (fun row => manyLeaves row.children) := by
  induction rows with
  | nil => simp only [edgeLeaves,List.flatMap_nil]
  | cons row rest ih =>
      cases row
      simp only [edgeLeaves,EdgeValue.children,List.flatMap_cons,ih]


end MicroCFTA.SourceCurrentOpenOrdinaryLeafSourceCalls
