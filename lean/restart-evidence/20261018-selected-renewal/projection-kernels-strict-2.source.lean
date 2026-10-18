import MicroCFTA.SourceCurrentProjectionIndexedOrigins
import MicroCFTA.SourceEqualityProjectionWorkerSound
import MicroCFTA.SourceEqualityProjectionCosts
import MicroCFTA.InternedFreshOrdinaryCosts
set_option linter.all true

namespace MicroCFTA.ProjectionIndexedKernels
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceEqualityProjectionGraph SourceEqualityProjectionUnion
local notation "Node" => Value Nat Unit
local notation "Edge" => EdgeValue Nat Unit
private def expression : InternedNestedConstruction.Syntax Nat Unit :=
  .node [.mk 0 () [],.mk 1 () [.node [.mk 2 () []]],.mk 3 () [.node [.mk 4 () []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def input : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def rows := nodeEdges input
private def values : List Node := rows.filterMap (fun row => select row.children 0)
private def selected : Node := values[1]?.getD .empty
private def united := SourceEqualityProjectionWorker.union 0 values heap
private def result : Node := match united with | .done value _ => value | _ => .empty
private def after := match united with | .done _ state => state | _ => heap
private def row : Edge := (nodeEdges result)[1]?.getD (run (makeEdge 9 () []) heap).1

private theorem built_done : built = .done input heap := by cbv
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression input heap built_done
private theorem available : Available heap input :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result input heap built_done
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  simpa only [built,heap] using InternedFreshOrdinaryCosts.closed_heap expression
private theorem actual_rows : SourceEqualityProjectionWorker.rows
    (SourceEqualityProjectionWorker.project 1 0 []) 0 rows heap = .done values heap := by cbv
private theorem projected : ProjectRows [] 0 rows heap values heap :=
  SourceEqualityProjectionWorkerSound.rows_graph (SourceEqualityProjectionWorker.project 1 0 []) []
    (fun value before result after actual =>
      SourceEqualityProjectionWorkerSound.project_graph 1 0 [] value before result after actual)
    0 rows heap values heap actual_rows
private theorem actual_union : united = .done result after := by cbv
private theorem combined : Union values heap result after :=
  SourceEqualityProjectionWorkerSound.union_graph 0 values heap result after actual_union
private theorem operands : InternedNestedProvenance.Values heap values :=
  (SourceEqualityProjectionCosts.rows_effects projected semantic costs
    (resident_edges heap semantic.ready.semantic.1.normal.facts.linked input available.resident)).2.2.2
private theorem closed : MergedColdReaderClosedInputs.ClosedValues values := by
  intro value member
  have shape : values = [values[0]?.getD .empty,values[1]?.getD .empty] := by cbv
  rw [shape] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> cbv

/-- Actual construction and projection exercise a skipped row and a later surviving union row. -/
theorem actual_skipped_rows_and_union :
    ∃ (program : InternedNestedConstruction.Syntax Nat Unit) (original : Node) (initial : State Nat Unit)
        (sourceRows : List Edge) (outputs : List Node) (chosen : Node)
        (output : Node) (final : State Nat Unit) (survivor : Edge),
      InternedFreshOrdinaryConstruction.build program [] empty = .done original initial ∧
      sourceRows = nodeEdges original ∧
      SourceEqualityProjectionWorker.rows (SourceEqualityProjectionWorker.project 1 0 []) 0
        sourceRows initial = .done outputs initial ∧
      sourceRows.length = 3 ∧ outputs.length = 2 ∧ outputs[1]? = some chosen ∧
      (∃ sourceIndex source child start finish,
        sourceRows[sourceIndex]? = some source ∧ select source.children 0 = some child ∧
        ProjectRows [] 0 (sourceRows.take sourceIndex) initial (outputs.take 1) start ∧
        Project [] child start chosen finish ∧
        ProjectRows [] 0 (sourceRows.drop (sourceIndex + 1)) finish (outputs.drop 2) initial) ∧
      Union outputs initial output final ∧
      survivor ∈ nodeEdges output ∧
      (∃ sourceIndex source earlierRows selectedRows laterRows start finish raw middle,
        outputs[sourceIndex]? = some source ∧
        ReadAll (outputs.take sourceIndex) initial earlierRows start ∧
        SourceEqualityProjectionRead.Read source start selectedRows finish ∧
        ReadAll (outputs.drop (sourceIndex + 1)) finish laterRows middle ∧
        raw = earlierRows ++ selectedRows ++ laterRows ∧ survivor ∈ selectedRows ∧
        ReadAll outputs initial raw middle ∧ run (makeNode raw) middle = (output,final) ∧
        EqualityLeafProjectionPhysical.dead survivor = false) := by
  have selectedAt : values[1]? = some selected := by cbv
  have survivor : row ∈ nodeEdges result := by cbv; simp
  exact ⟨expression,input,heap,rows,values,selected,result,after,row,built_done,rfl,actual_rows,
    by cbv,by cbv,selectedAt,
    SourceCurrentProjectionIndexedOrigins.rows_indexed projected 1 selected selectedAt,
    combined,survivor,
    SourceCurrentProjectionIndexedOrigins.union_row combined semantic operands closed row survivor⟩

end MicroCFTA.ProjectionIndexedKernels
