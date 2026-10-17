import MicroCFTA.SourceCurrentSharedEditRowLineage
import MicroCFTA.SourceCurrentParentNativeHistory

/-!
# Actual writer histories at surviving edited rows

The exact earlier-row execution connects initial native history to each
captured row start. The actual child reads then produce history at that
row's constructor. Both captured heaps grow into the final node reader.
This result does not establish future outer completion or owner exclusion.
-/
namespace MicroCFTA.SourceCurrentParentRowWriterLineage
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Edges)
open SourceEqualityEdits SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Surviving row origins carry the native histories produced by their actual execution prefixes. -/
theorem node_survivor {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals entries edges before rebuilt middle memos final value heap}
    {actual : EditRows (width := width) record originals entries edges before rebuilt middle}
    (reads : RowsReads formulas solver base actual memos final)
    (built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap))
    (inventory : Inventory) (populated : Populated (.editBelow entries))
    (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (resident : Edges before.checked.native.machine.heap edges) (safe : RowsSafe entries edges)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (history : History before.checked)
    {row : EdgeValue Symbol Guard} (selected : row ∈ InternedEdgeResidency.nodeEdges value) :
    ∃ index : Nat, ∃ original : EdgeValue Symbol Guard, ∃ start rowMiddle : SharedState width,
    ∃ values rowHeap rowMemos rowFinal,
    ∃ call : EditChildren record originals entries 0 original.children start values rowMiddle,
      rebuilt[index]? = some row ∧ edges[index]? = some original ∧
      ChildrenReads formulas solver base call rowMemos rowFinal ∧
      run (makeEdge original.entry.key.symbol original.entry.key.constraint values)
        rowMiddle.checked.native.machine.heap = (row, rowHeap) ∧
      row.entry.key.symbol = original.entry.key.symbol ∧
      row.entry.key.constraint = original.entry.key.constraint ∧ row.children = values ∧
      History start.checked ∧ History rowMiddle.checked ∧
      Grows start.checked.native.machine.heap heap ∧
      Grows rowMiddle.checked.native.machine.heap heap ∧ Grows rowHeap heap ∧
      EqualityLeafProjectionPhysical.dead row = false := by
  obtain ⟨index, original, start, rowMiddle, values, rowHeap, startInventory, middleInventory,
    rowMemos, rowFinal, earlierRows, call, rawIndex, sourceIndex, prefixReads, childReads, startValid,
    edgeBuilt, symbol, guard, children, startReady, middleReady, startGrowth, middleGrowth, heapGrowth, live⟩ :=
    SourceCurrentSharedEditRowLineage.node_survivor reads built inventory populated allowed ready resident safe valid selected
  have startHistory := SourceCurrentParentNativeHistory.edit_rows prefixReads history
    ready.checked.semantic.ready.semantic.1.normal.facts.coherent.valid
  have middleHistory := SourceCurrentParentNativeHistory.edit_children childReads startHistory.1 startHistory.2
  exact ⟨index, original, start, rowMiddle, values, rowHeap, rowMemos, rowFinal, call, rawIndex, sourceIndex,
    childReads, edgeBuilt, symbol, guard, children, startHistory.1, middleHistory.1,
    startGrowth, middleGrowth, heapGrowth, live⟩

end MicroCFTA.SourceCurrentParentRowWriterLineage
