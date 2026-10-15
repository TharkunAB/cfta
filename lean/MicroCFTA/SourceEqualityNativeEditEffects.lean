import MicroCFTA.SourceEqualityNativeEditGraph

/-!
# Scoped cache effects of simultaneous native edits

Captured targets belong to one real earlier cache. Actual histories keep
them available at every leaf. Native validity and idle memo state follow
from actual native requests and constructor effects, not a global leaf law.
-/
namespace MicroCFTA.SourceEqualityNativeEditEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityEdits SourceEqualityNativeEditGraph

/-- Every retained leaf target is closed and available in the actual base cache. -/
def Captured (base : InternedConstructorTemplates.State Symbol Guard) (edits : Edits (Value Symbol Guard)) : Prop :=
  All (fun target => Available base target ∧ target.free = []) edits

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (base : InternedConstructorTemplates.State Symbol Guard)

private def NodeEffects (edits : Edits (Value Symbol Guard)) (value : Value Symbol Guard)
    (before : NativeState width Symbol Guard) (result : Value Symbol Guard) (after : NativeState width Symbol Guard) : Prop :=
  Captured base edits → Keeps base before.machine.heap → IdleReady emptyGuard conjoin before →
    Available before.machine.heap value → value.free = [] →
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = []

private def ChildrenEffects (entries : List (Int × Edits (Value Symbol Guard))) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (results : List (Value Symbol Guard)) (after : NativeState width Symbol Guard) : Prop :=
  Captured base (.editBelow entries) → Keeps base before.machine.heap → IdleReady emptyGuard conjoin before →
    Values before.machine.heap values → ClosedValues values →
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results

private def RowsEffects (entries : List (Int × Edits (Value Symbol Guard))) (edges : List (EdgeValue Symbol Guard))
    (before : NativeState width Symbol Guard) (results : List (EdgeValue Symbol Guard)) (after : NativeState width Symbol Guard) : Prop :=
  Captured base (.editBelow entries) → Keeps base before.machine.heap → IdleReady emptyGuard conjoin before →
    Edges before.machine.heap edges → ClosedEdges edges →
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Edges after.machine.heap results ∧ ClosedEdges results

local notation "NodeLaw" => NodeEffects (width := width) emptyGuard conjoin base
local notation "ChildrenLaw" => ChildrenEffects (width := width) emptyGuard conjoin base
local notation "RowsLaw" => RowsEffects (width := width) emptyGuard conjoin base

private theorem effects :
    (∀ edits (value : Value Symbol Guard) (before : NativeState width Symbol Guard) result after,
      EditNode emptyGuard conjoin edits value before result after → NodeLaw edits value before result after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) results after,
      EditChildren emptyGuard conjoin entries index values before results after → ChildrenLaw entries values before results after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) (before : NativeState width Symbol Guard) results after,
      EditRows emptyGuard conjoin entries edges before results after → RowsLaw entries edges before results after) := by
  have leafCase : ∀ {target value before result after}, Step emptyGuard conjoin target value before result after →
      NodeLaw (.editAt target) value before result after := by
    intro target value before result after step captured retained ready available closed
    have known : Available base target ∧ target.free = [] := by simpa only [Captured, All] using captured
    have checked := step.verified ready (retained.available target known.1) available known.2 closed
      (fun _ _ => true) (by intros; rfl)
    exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩
  have emptyCase : ∀ {entries state}, NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) state .empty state := by
    intro entries state _ _ ready available closed
    exact ⟨ready, pure_keeps _ ready.semantic.ready, available, closed⟩
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap entry depth free},
      EditRows emptyGuard conjoin entries edges before rebuilt middle →
      run (makeNode rebuilt) middle.machine.heap = (value, heap) → RowsLaw entries edges before rebuilt middle →
      NodeLaw (.editBelow entries) (.node entry edges depth free) before value (advanceHeap middle heap) := by
    intro entries edges before rebuilt middle value heap entry depth free _ built rowsIH captured retained ready available closed
    have facts := ready.semantic.ready.semantic.1.normal.facts
    have rows := rowsIH captured retained ready
      (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident)
      (MergedColdReaderClosed.node_children_closed _ facts entry edges depth free available closed)
    have finished := SourceEqualityRequiredCache.node rebuilt middle.machine.heap rows.1.semantic.ready rows.2.2.1 rows.2.2.2
    have semantic := SourceEqualityRequiredSemanticCache.node rebuilt middle.machine.heap rows.1.semantic rows.2.2.1 rows.2.2.2
    have kept : Keeps middle.machine.heap heap := by simpa only [built] using finished.1
    have semanticHeap : SemanticReady heap := by simpa only [built] using semantic
    refine ⟨rows.1.advance heap kept semanticHeap, rows.2.1.trans kept, ?_, ?_⟩
    · change Available heap value
      simpa only [built] using finished.2.1
    · simpa only [built] using finished.2.2.1
  have recursiveCase : ∀ {entries original before exposed heap result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before.machine.heap exposed heap →
      EditNode emptyGuard conjoin (.editBelow entries) exposed (advanceHeap before heap) result after →
      NodeLaw (.editBelow entries) exposed (advanceHeap before heap) result after → NodeLaw (.editBelow entries) original before result after := by
    intro entries original before exposed heap result after _ head _ ih captured retained ready available closed
    have first := head.verified ready.semantic.ready available closed
    have semantic := SourceEqualityRequiredSemanticCache.head head ready.semantic available closed
    have later := ih captured (retained.trans first.1) (ready.advance heap first.1 semantic) first.2.1 first.2.2.1
    exact ⟨later.1, first.1.trans later.2.1, later.2.2⟩
  have nilChildren : ∀ {entries state}, ChildrenLaw entries ([] : List (Value Symbol Guard)) state [] state := by
    intro entries state _ _ ready _ _
    exact ⟨ready, pure_keeps _ ready.semantic.ready, by simp [Values], by simp [ClosedValues]⟩
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none → EditChildren emptyGuard conjoin entries (index + 1) values before results after →
      ChildrenLaw entries values before results after → ChildrenLaw entries (value :: values) before (value :: results) after := by
    intro entries values before results after value index _ _ ih captured retained ready available closed
    have rest := ih captured retained ready (fun child member => available child (List.mem_cons_of_mem _ member))
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
      SourceEqualityNeededMap.lookup (index : Int) entries = some edits → EditNode emptyGuard conjoin edits value before result middle →
      EditChildren emptyGuard conjoin entries (index + 1) values middle results after →
      NodeLaw edits value before result middle → ChildrenLaw entries values middle results after →
      ChildrenLaw entries (value :: values) before (result :: results) after := by
    intro entries edits value before result middle values results after index found _ _ firstIH restIH captured retained ready available closed
    have childCaptured : Captured base edits := by
      have all := captured
      rw [Captured, All] at all
      exact all (index : Int) edits (SourceEqualityNeededMap.lookup_mem _ _ _ found)
    have first := firstIH childCaptured retained ready (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
    have rest := restIH captured (retained.trans first.2.1) first.1
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
    intro entries state _ _ ready _ _
    exact ⟨ready, pure_keeps _ ready.semantic.ready, by simp [Edges], by simp [ClosedEdges]⟩
  have consCase : ∀ {entries before values middle result heap edges results after edge},
      EditChildren emptyGuard conjoin entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.machine.heap = (result, heap) →
      EditRows emptyGuard conjoin entries edges (advanceHeap middle heap) results after → ChildrenLaw entries edge.children before values middle →
      RowsLaw entries edges (advanceHeap middle heap) results after → RowsLaw entries (edge :: edges) before (result :: results) after := by
    intro entries before values middle result heap edges results after edge _ built _ childIH restIH captured retained ready resident closed
    have facts := ready.semantic.ready.semantic.1.normal.facts
    have children := childIH captured retained ready (facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self))
      (closed edge List.mem_cons_self)
    have rebuilt := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.machine.heap
      children.1.semantic.ready children.2.2.1
    have semantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.machine.heap
      children.1.semantic children.2.2.1
    have edgeKeeps : Keeps middle.machine.heap heap := by simpa only [built] using rebuilt.1
    have heapSemantic : SemanticReady heap := by simpa only [built] using semantic
    have edgeResident : InternedEdgeResidency.EdgeResident heap result := by simpa only [built] using rebuilt.2.1
    have edgeChildren : result.children = values := by simpa only [built] using rebuilt.2.2
    have firstKeeps := children.2.1.trans edgeKeeps
    have rest := restIH captured (retained.trans firstKeeps) (children.1.advance heap edgeKeeps heapSemantic)
      (fun original member => InternedEdgeResidency.edge_grows before.machine.heap heap firstKeeps.growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => closed original (List.mem_cons_of_mem _ member))
    refine ⟨rest.1, firstKeeps.trans rest.2.1, ?_, ?_⟩
    · intro output member
      rcases List.mem_cons.mp member with rfl | tail
      · exact InternedEdgeResidency.edge_grows heap after.machine.heap rest.2.1.growth _ edgeResident
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
theorem node {edits value before result after} (trace : EditNode (width := width) emptyGuard conjoin edits value before result after) :
    NodeLaw edits value before result after := (effects emptyGuard conjoin base).1 _ _ _ _ _ trace

/-- Complete child scans retain all original positions and closed native results. -/
theorem children {entries index values before results after}
    (trace : EditChildren (width := width) emptyGuard conjoin entries index values before results after) :
    ChildrenLaw entries values before results after := (effects emptyGuard conjoin base).2.1 _ _ _ _ _ _ trace

/-- Complete row scans retain full resident and closed edge payloads. -/
theorem rows {entries edges before results after}
    (trace : EditRows (width := width) emptyGuard conjoin entries edges before results after) :
    RowsLaw entries edges before results after := (effects emptyGuard conjoin base).2.2 _ _ _ _ _ trace

end MicroCFTA.SourceEqualityNativeEditEffects
