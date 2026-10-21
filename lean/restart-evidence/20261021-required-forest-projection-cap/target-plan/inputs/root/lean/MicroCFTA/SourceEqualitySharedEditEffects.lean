import MicroCFTA.SourceEqualitySharedEditGraph

/-!
# Scoped effects of simultaneous edits with shared target closures

Original class paths validate every callback token. Leaves derive target
availability by first forcing or reuse. Every constructor retains stored
receipts and the actual full native state. No eager target scope is assumed.
-/
namespace MicroCFTA.SourceEqualitySharedEditEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualitySharedTargetState SourceEqualitySharedTargetLeaf
open SourceEqualityEdits SourceEqualitySharedEditGraph

/-- Every compiled leaf token denotes a path of the original physical class. -/
def Allowed (record : SourceEqualityClassOrder.Record) (edits : Edits EqualityNormalize.Path) : Prop :=
  All (fun path => path ∈ record.paths) edits

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard)
variable (known : Values base originals) (originalClosed : ClosedValues originals)

private def NodeEffects (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard)
    (before : SharedState width Symbol Guard) (result : Value Symbol Guard) (after : SharedState width Symbol Guard) : Prop :=
  Allowed record edits → Ready emptyGuard conjoin clear top record originals base before →
    Available before.native.machine.heap value → value.free = [] →
    Ready emptyGuard conjoin clear top record originals base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧ Available after.native.machine.heap result ∧ result.free = []

private def ChildrenEffects (entries : List (Int × Edits EqualityNormalize.Path)) (values : List (Value Symbol Guard))
    (before : SharedState width Symbol Guard) (results : List (Value Symbol Guard)) (after : SharedState width Symbol Guard) : Prop :=
  Allowed record (.editBelow entries) → Ready emptyGuard conjoin clear top record originals base before →
    Values before.native.machine.heap values → ClosedValues values →
    Ready emptyGuard conjoin clear top record originals base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧ Values after.native.machine.heap results ∧ ClosedValues results

private def RowsEffects (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard))
    (before : SharedState width Symbol Guard) (results : List (EdgeValue Symbol Guard)) (after : SharedState width Symbol Guard) : Prop :=
  Allowed record (.editBelow entries) → Ready emptyGuard conjoin clear top record originals base before →
    Edges before.native.machine.heap edges → ClosedEdges edges →
    Ready emptyGuard conjoin clear top record originals base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧ Edges after.native.machine.heap results ∧ ClosedEdges results

local notation "NodeLaw" => NodeEffects (width := width) emptyGuard conjoin clear top record originals base
local notation "ChildrenLaw" => ChildrenEffects (width := width) emptyGuard conjoin clear top record originals base
local notation "RowsLaw" => RowsEffects (width := width) emptyGuard conjoin clear top record originals base

include known originalClosed

private theorem effects :
    (∀ edits (value : Value Symbol Guard) (before : SharedState width Symbol Guard) result after,
      EditNode emptyGuard conjoin clear top record originals edits value before result after → NodeLaw edits value before result after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) (before : SharedState width Symbol Guard) results after,
      EditChildren emptyGuard conjoin clear top record originals entries index values before results after → ChildrenLaw entries values before results after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) (before : SharedState width Symbol Guard) results after,
      EditRows emptyGuard conjoin clear top record originals entries edges before results after → RowsLaw entries edges before results after) := by
  have leafCase : ∀ {target value before result after}, Leaf emptyGuard conjoin clear top record originals target value before result after →
      NodeLaw (.editAt target) value before result after := by
    intro target value before result after step captured ready available closed
    have member : target ∈ record.paths := by simpa only [Allowed, All] using captured
    have checked := step.effects ready known originalClosed member available closed
    exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩
  have emptyCase : ∀ {entries state}, NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) state .empty state := by
    intro entries state _ ready available closed
    exact ⟨ready, pure_keeps _ ready.native.semantic.ready, available, closed⟩
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap entry depth free},
      EditRows emptyGuard conjoin clear top record originals entries edges before rebuilt middle →
      run (makeNode rebuilt) middle.native.machine.heap = (value, heap) → RowsLaw entries edges before rebuilt middle →
      NodeLaw (.editBelow entries) (.node entry edges depth free) before value (advanceHeap middle heap) := by
    intro entries edges before rebuilt middle value heap entry depth free _ built rowsIH captured ready available closed
    have facts := ready.native.semantic.ready.semantic.1.normal.facts
    have rows := rowsIH captured ready
      (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident)
      (MergedColdReaderClosed.node_children_closed _ facts entry edges depth free available closed)
    have finished := SourceEqualityRequiredCache.node rebuilt middle.native.machine.heap rows.1.native.semantic.ready rows.2.2.1 rows.2.2.2
    have semantic := SourceEqualityRequiredSemanticCache.node rebuilt middle.native.machine.heap rows.1.native.semantic rows.2.2.1 rows.2.2.2
    have kept : Keeps middle.native.machine.heap heap := by simpa only [built] using finished.1
    have semanticHeap : SemanticReady heap := by simpa only [built] using semantic
    refine ⟨rows.1.heap heap kept semanticHeap, rows.2.1.trans kept, ?_, ?_⟩
    · change Available heap value
      simpa only [built] using finished.2.1
    · simpa only [built] using finished.2.2.1
  have recursiveCase : ∀ {entries original before exposed heap result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap →
      EditNode emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap) result after →
      NodeLaw (.editBelow entries) exposed (advanceHeap before heap) result after → NodeLaw (.editBelow entries) original before result after := by
    intro entries original before exposed heap result after _ head _ ih captured ready available closed
    have first := head.verified ready.native.semantic.ready available closed
    have semantic := SourceEqualityRequiredSemanticCache.head head ready.native.semantic available closed
    have later := ih captured (ready.heap heap first.1 semantic) first.2.1 first.2.2.1
    exact ⟨later.1, first.1.trans later.2.1, later.2.2⟩
  have nilChildren : ∀ {entries state}, ChildrenLaw entries ([] : List (Value Symbol Guard)) state [] state := by
    intro entries state _ ready _ _
    exact ⟨ready, pure_keeps _ ready.native.semantic.ready, by simp [Values], by simp [ClosedValues]⟩
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none → EditChildren emptyGuard conjoin clear top record originals entries (index + 1) values before results after →
      ChildrenLaw entries values before results after → ChildrenLaw entries (value :: values) before (value :: results) after := by
    intro entries values before results after value index _ _ ih captured ready available closed
    have rest := ih captured ready (fun child member => available child (List.mem_cons_of_mem _ member))
      (fun child member => closed child (List.mem_cons_of_mem _ member))
    refine ⟨rest.1, rest.2.1, ?_, ?_⟩
    · intro child member
      rcases List.mem_cons.mp member with rfl | tail
      · exact rest.2.1.available _ (available _ List.mem_cons_self)
      · exact rest.2.2.1 child tail
    · intro child member
      rcases List.mem_cons.mp member with rfl | tail
      · exact closed _ List.mem_cons_self
      · exact rest.2.2.2 child tail
  have selectedCase : ∀ {entries edits value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some edits → EditNode emptyGuard conjoin clear top record originals edits value before result middle →
      EditChildren emptyGuard conjoin clear top record originals entries (index + 1) values middle results after →
      NodeLaw edits value before result middle → ChildrenLaw entries values middle results after →
      ChildrenLaw entries (value :: values) before (result :: results) after := by
    intro entries edits value before result middle values results after index found _ _ firstIH restIH captured ready available closed
    have childCaptured : Allowed record edits := by
      have all := captured
      rw [Allowed, All] at all
      exact all (index : Int) edits (SourceEqualityNeededMap.lookup_mem _ _ _ found)
    have first := firstIH childCaptured ready (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
    have rest := restIH captured first.1
      (fun child member => first.2.1.available child (available child (List.mem_cons_of_mem _ member)))
      (fun child member => closed child (List.mem_cons_of_mem _ member))
    refine ⟨rest.1, first.2.1.trans rest.2.1, ?_, ?_⟩
    · intro child member
      rcases List.mem_cons.mp member with rfl | tail
      · exact rest.2.1.available _ first.2.2.1
      · exact rest.2.2.1 child tail
    · intro child member
      rcases List.mem_cons.mp member with rfl | tail
      · exact first.2.2.2
      · exact rest.2.2.2 child tail
  have nilRows : ∀ {entries state}, RowsLaw entries ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intro entries state _ ready _ _
    exact ⟨ready, pure_keeps _ ready.native.semantic.ready, by simp [Edges], by simp [ClosedEdges]⟩
  have consCase : ∀ {entries before values middle result heap edges results after edge},
      EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap = (result, heap) →
      EditRows emptyGuard conjoin clear top record originals entries edges (advanceHeap middle heap) results after → ChildrenLaw entries edge.children before values middle →
      RowsLaw entries edges (advanceHeap middle heap) results after → RowsLaw entries (edge :: edges) before (result :: results) after := by
    intro entries before values middle result heap edges results after edge _ built _ childIH restIH captured ready resident closed
    have facts := ready.native.semantic.ready.semantic.1.normal.facts
    have children := childIH captured ready (facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self))
      (closed edge List.mem_cons_self)
    have rebuilt := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      children.1.native.semantic.ready children.2.2.1
    have semantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      children.1.native.semantic children.2.2.1
    have edgeKeeps : Keeps middle.native.machine.heap heap := by simpa only [built] using rebuilt.1
    have heapSemantic : SemanticReady heap := by simpa only [built] using semantic
    have edgeResident : InternedEdgeResidency.EdgeResident heap result := by simpa only [built] using rebuilt.2.1
    have edgeChildren : result.children = values := by simpa only [built] using rebuilt.2.2
    have firstKeeps := children.2.1.trans edgeKeeps
    have rest := restIH captured (children.1.heap heap edgeKeeps heapSemantic)
      (fun original member => InternedEdgeResidency.edge_grows before.native.machine.heap heap firstKeeps.growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => closed original (List.mem_cons_of_mem _ member))
    refine ⟨rest.1, firstKeeps.trans rest.2.1, ?_, ?_⟩
    · intro output member
      rcases List.mem_cons.mp member with rfl | tail
      · exact InternedEdgeResidency.edge_grows heap after.native.machine.heap rest.2.1.growth _ edgeResident
      · exact rest.2.2.1 output tail
    · intro output member
      rcases List.mem_cons.mp member with rfl | tail
      · simpa only [edgeChildren] using children.2.2.2
      · exact rest.2.2.2 output tail
  refine ⟨?_, ?_, ?_⟩
  · intro edits value before result after trace
    exact EditNode.rec (motive_1 := fun edits value before result after _ => NodeLaw edits value before result after)
      (motive_2 := fun entries _ values before results after _ => ChildrenLaw entries values before results after)
      (motive_3 := fun entries edges before results after _ => RowsLaw entries edges before results after)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase trace
  · intro entries index values before results after trace
    exact EditChildren.rec (motive_1 := fun edits value before result after _ => NodeLaw edits value before result after)
      (motive_2 := fun entries _ values before results after _ => ChildrenLaw entries values before results after)
      (motive_3 := fun entries edges before results after _ => RowsLaw entries edges before results after)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase trace
  · intro entries edges before results after trace
    exact EditRows.rec (motive_1 := fun edits value before result after _ => NodeLaw edits value before result after)
      (motive_2 := fun entries _ values before results after _ => ChildrenLaw entries values before results after)
      (motive_3 := fun entries edges before results after _ => RowsLaw entries edges before results after)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase trace

/-- Complete node edits derive scoped native and constructor cache effects at every intermediate state. -/
theorem node {edits value before result after} (trace : EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result after) :
    NodeLaw edits value before result after := (effects emptyGuard conjoin clear top record originals base known originalClosed).1 _ _ _ _ _ trace

/-- Complete child scans retain all original positions and closed native results. -/
theorem children {entries index values before results after}
    (trace : EditChildren (width := width) emptyGuard conjoin clear top record originals entries index values before results after) :
    ChildrenLaw entries values before results after := (effects emptyGuard conjoin clear top record originals base known originalClosed).2.1 _ _ _ _ _ _ trace

/-- Complete row scans retain full resident and closed edge payloads. -/
theorem rows {entries edges before results after}
    (trace : EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before results after) :
    RowsLaw entries edges before results after := (effects emptyGuard conjoin clear top record originals base known originalClosed).2.2 _ _ _ _ _ trace

end MicroCFTA.SourceEqualitySharedEditEffects
