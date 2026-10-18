import MicroCFTA.SourceEqualityProjectionGraph
import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Indexed sources in actual path projection schedules

Missing child positions do not produce output positions. Each returned
projection retains its exact input row and earlier and later calls.
A surviving union row retains the actual operand read that supplied it.
The operand read can unfold Mu. These results do not identify an initial
source occurrence or establish a decreasing rank for outer reduction.
-/
namespace MicroCFTA.SourceCurrentProjectionIndexedOrigins
open InternedConstructorTemplates InternedEdgeResidency
open SourceEqualityProjectionGraph SourceEqualityProjectionUnion
open SourceEqualityProjectionRead
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Each output position retains its selected input row and exact projection prefix and suffix. -/
theorem rows_indexed {path index edges before results after}
    (actual : ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after)
    (position : Nat) (value : Value Symbol Guard) (selected : results[position]? = some value) :
    ∃ sourceIndex source child start finish,
      edges[sourceIndex]? = some source ∧ select source.children index = some child ∧
      ProjectRows path index (edges.take sourceIndex) before (results.take position) start ∧
      Project path child start value finish ∧
      ProjectRows path index (edges.drop (sourceIndex + 1)) finish (results.drop (position + 1)) after := by
  induction actual generalizing position with
  | nil => cases selected
  | @missing source path index edges before results after absent rest ih =>
    obtain ⟨sourceIndex,original,child,start,finish,found,chosen,earlier,called,later⟩ :=
      ih position selected
    exact ⟨sourceIndex + 1,original,child,start,finish,
      by simpa only [List.getElem?_cons_succ] using found,
      chosen,by simpa only [List.take_succ_cons] using ProjectRows.missing absent earlier,
      called,by simpa only [Nat.add_assoc,List.drop_succ_cons] using later⟩
  | @selected source index child path before result middle edges results after found first rest ih =>
    cases position with
    | zero =>
      cases Option.some.inj selected
      exact ⟨0,source,child,before,middle,rfl,found,.nil,first,rest⟩
    | succ position =>
      obtain ⟨sourceIndex,original,child,start,finish,present,chosen,earlier,called,later⟩ :=
        ih position (by simpa only [List.getElem?_cons_succ] using selected)
      exact ⟨sourceIndex + 1,original,child,start,finish,
        by simpa only [List.getElem?_cons_succ] using present,
        chosen,by simpa only [List.take_succ_cons] using ProjectRows.selected found first earlier,
        called,by simpa only [Nat.add_assoc,List.drop_succ_cons] using later⟩

private theorem read_all_member {values before edges after}
    (actual : ReadAll (Symbol := Symbol) (Guard := Guard) values before edges after)
    (row : EdgeValue Symbol Guard) (member : row ∈ edges) :
    ∃ sourceIndex source earlierRows selectedRows laterRows start finish,
      values[sourceIndex]? = some source ∧
      ReadAll (values.take sourceIndex) before earlierRows start ∧
      Read source start selectedRows finish ∧
      ReadAll (values.drop (sourceIndex + 1)) finish laterRows after ∧
      edges = earlierRows ++ selectedRows ++ laterRows ∧ row ∈ selectedRows := by
  induction actual with
  | nil => cases member
  | @cons source before rows middle values more after first rest ih =>
    rcases List.mem_append.mp member with here | later
    · exact ⟨0,source,[],rows,more,before,middle,rfl,.nil,first,rest,rfl,here⟩
    · obtain ⟨sourceIndex,original,earlierRows,selectedRows,laterRows,start,finish,
        found,earlier,called,later,parts,present⟩ := ih later
      refine ⟨sourceIndex + 1,original,rows ++ earlierRows,selectedRows,laterRows,start,finish,
        ?_,?_,called,?_,?_,present⟩
      · simpa only [List.getElem?_cons_succ] using found
      · simpa only [List.take_succ_cons] using ReadAll.cons first earlier
      · simpa only [Nat.add_assoc,List.drop_succ_cons] using later
      · simp only [parts,List.append_assoc]

/-- Each surviving union row retains one indexed operand and its literal row read and schedules. -/
theorem union_row {values before result after}
    (actual : Union (Symbol := Symbol) (Guard := Guard) values before result after)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (available : InternedNestedProvenance.Values before values)
    (closed : MergedColdReaderClosedInputs.ClosedValues values)
    (row : EdgeValue Symbol Guard) (member : row ∈ nodeEdges result) :
    ∃ sourceIndex source earlierRows selectedRows laterRows start finish rows middle,
      values[sourceIndex]? = some source ∧
      ReadAll (values.take sourceIndex) before earlierRows start ∧
      Read source start selectedRows finish ∧
      ReadAll (values.drop (sourceIndex + 1)) finish laterRows middle ∧
      rows = earlierRows ++ selectedRows ++ laterRows ∧ row ∈ selectedRows ∧
      ReadAll values before rows middle ∧ run (makeNode rows) middle = (result,after) ∧
      EqualityLeafProjectionPhysical.dead row = false := by
  cases actual with
  | node reads built =>
    have facts := reads.verified semantic available closed
    have exactRows := EqualityLeafProjectionPhysical.makeNode_edges _ _
      facts.2.1.ready.semantic.1.normal.facts.coherent
      facts.2.1.ready.semantic.1.normal.facts.linked facts.2.2.1
    rw [built] at exactRows
    have kept := (EqualityLeafProjectionPhysical.normalized_member _
      facts.2.1.ready.semantic.1.normal.facts.coherent _ facts.2.2.1 row).mp
      (exactRows ▸ member)
    obtain ⟨sourceIndex,source,earlierRows,selectedRows,laterRows,start,finish,
      found,earlier,called,later,parts,present⟩ := read_all_member reads row kept.1
    exact ⟨sourceIndex,source,earlierRows,selectedRows,laterRows,start,finish,_,_,
      found,earlier,called,later,parts,present,reads,built,kept.2⟩

end MicroCFTA.SourceCurrentProjectionIndexedOrigins
