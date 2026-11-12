import MicroCFTA.SourceNativeOrdinaryRows
import MicroCFTA.SymbolicStructuralBudget

/-!
# Structural budget of the current ordinary native snapshot

The rank reads ordinary height from the actual current payload.
Every snapshot row decreases this rank, including unrelated ordinary rows.
Recursive and union records have no ordinary snapshot rows.
This budget does not interpret the full retained recursive heap.
-/
namespace MicroCFTA.SourceNativeOrdinaryRowsBudget
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedFacts InternedEdgeResidency
open SourcePreparedSharedRows (read reference encode exposure)

/-- Empty and absent states have rank zero; actual native IDs use their stored payload height. -/
def rank (state : State Symbol Guard) : SourceInternedRows.State → Nat
  | .empty => 0
  | .interned identity => ((read state identity).map MergedOrdinaryHeight.height).getD 0

/-- Current available payloads have their exact ordinary height at their encoded state. -/
theorem rank_encode (state : State Symbol Guard) (facts : Facts state) (value : Value Symbol Guard)
    (available : Available state value) : rank state (encode value) = MergedOrdinaryHeight.height value := by
  cases value with
  | empty => simp only [encode, reference, SourceInternedRows.stateOf, rank, MergedOrdinaryHeight.height]
  | reference name => simp only [encode, reference, SourceInternedRows.stateOf, rank, MergedOrdinaryHeight.height]
  | node entry edges depth free | union entry members depth free | mu entry body depthShape ordinaryShape =>
      have found := SourcePreparedSharedRows.read_identity state facts _ available entry.identity rfl
      simp only [encode, reference, SourceInternedRows.stateOf, rank, found, Option.map_some, Option.getD_some]

private theorem child_height_lt (value : Value Symbol Guard) (edge : EdgeValue Symbol Guard)
    (member : edge ∈ nodeEdges value) (child : Value Symbol Guard) (inside : child ∈ edge.children) :
    MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height value := by
  cases value
  case node entry edges depth free =>
    exact MergedOrdinaryHeight.child_lt entry edges depth free edge member child inside
  all_goals
    simp only [nodeEdges, List.not_mem_nil] at member

/-- Every row of the current ordinary snapshot strictly decreases the actual read-based rank. -/
theorem rank_strict (state : State Symbol Guard) (facts : Facts state) (holds : Guard → Term Symbol → Bool)
    (source : SourceInternedRows.State) (edge : Language.Edge SourceInternedRows.State Symbol)
    (member : edge ∈ SourceInternedRows.graph (SourceNativeOrdinaryRows.heap state) holds source)
    (child : SourceInternedRows.State) (inside : child ∈ edge.children) :
    rank state child < rank state source := by
  cases source with
  | empty => simp only [SourceInternedRows.graph, List.not_mem_nil] at member
  | interned identity =>
      obtain ⟨row, rowIn, rfl⟩ := List.mem_map.mp member
      obtain ⟨nativeEdge, edgeIn, rfl⟩ := List.mem_map.mp rowIn
      obtain ⟨parent, parentIn, edgeIn⟩ := List.mem_flatMap.mp edgeIn
      have found : read state identity = some parent := Option.mem_toList.mp parentIn
      have available := SourcePreparedSharedRows.read_available state facts identity parent found
      have parentRank : rank state (.interned identity) = MergedOrdinaryHeight.height parent := by
        simp only [rank, found, Option.map_some, Option.getD_some]
      have mapped : child ∈ nativeEdge.children.map encode := by
        have same : nativeEdge.children.map encode =
            (nativeEdge.children.map reference).map SourceInternedRows.stateOf := by
          rw [List.map_map]
          rfl
        rw [same]
        exact inside
      obtain ⟨nativeChild, childIn, same⟩ := List.mem_map.mp mapped
      subst child
      have childAvailable := SourceNativeOrdinaryRows.child_available state facts parent available nativeEdge edgeIn nativeChild childIn
      rw [rank_encode state facts nativeChild childAvailable, parentRank]
      exact child_height_lt parent nativeEdge edgeIn nativeChild childIn

/-- Current native row readback instantiates the existing complete structural budget. -/
def budget (state : State Symbol Guard) (facts : Facts state) (holds : Guard → Term Symbol → Bool) :
    GraphBudget.Budget (SourceInternedRows.graph (SourceNativeOrdinaryRows.heap state) holds) :=
  SymbolicGraphView.structuralBudget _ (rank state) (rank_strict state facts holds)

end MicroCFTA.SourceNativeOrdinaryRowsBudget
