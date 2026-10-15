import MicroCFTA.SourceEqualityAnnotationTarget
import MicroCFTA.SourceEqualitySharedEditEffects

/-!
# Physical annotation heaps through simultaneous shared target edits

The mutual graph proof follows actual first forcing, target reuse, native
intersection, head reads, child scans, and literal full-guard row requests.
Original capture scopes and warm native states come from source effects.
No completed edit annotation heap is supplied as a premise.
-/
namespace MicroCFTA.SourceEqualityAnnotationSharedEdit
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualitySharedTargetState SourceEqualitySharedTargetLeaf
open SourceEqualityEdits SourceEqualitySharedEditGraph
open SourceEqualitySharedEditEffects (Allowed)
open SourceEqualityAnnotationHeap (Heap)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (annotation : Guard → Prop) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard)
variable (known : Values base originals) (originalClosed : ClosedValues originals)
variable (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)

private def NodePreserved (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard)
    (before after : SharedState width Symbol Guard) : Prop :=
  Allowed record edits → Ready emptyGuard conjoin clear top record originals base before →
    Available before.native.machine.heap value → value.free = [] → Heap annotation before.native.machine.heap → Heap annotation after.native.machine.heap

private def ChildrenPreserved (entries : List (Int × Edits EqualityNormalize.Path)) (values : List (Value Symbol Guard))
    (before after : SharedState width Symbol Guard) : Prop :=
  Allowed record (.editBelow entries) → Ready emptyGuard conjoin clear top record originals base before →
    Values before.native.machine.heap values → ClosedValues values → Heap annotation before.native.machine.heap → Heap annotation after.native.machine.heap

private def RowsPreserved (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard))
    (before after : SharedState width Symbol Guard) : Prop :=
  Allowed record (.editBelow entries) → Ready emptyGuard conjoin clear top record originals base before →
    Edges before.native.machine.heap edges → ClosedEdges edges → Heap annotation before.native.machine.heap → Heap annotation after.native.machine.heap

local notation "NodeLaw" => NodePreserved (width := width) annotation emptyGuard conjoin clear top record originals base
local notation "ChildrenLaw" => ChildrenPreserved (width := width) annotation emptyGuard conjoin clear top record originals base
local notation "RowsLaw" => RowsPreserved (width := width) annotation emptyGuard conjoin clear top record originals base

include known originalClosed emptyValid conjoinedValid topValid

private theorem all_preserved :
    (∀ edits (value : Value Symbol Guard) (before : SharedState width Symbol Guard) result after,
      EditNode emptyGuard conjoin clear top record originals edits value before result after → NodeLaw edits value before after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) (before : SharedState width Symbol Guard) results after,
      EditChildren emptyGuard conjoin clear top record originals entries index values before results after → ChildrenLaw entries values before after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) (before : SharedState width Symbol Guard) results after,
      EditRows emptyGuard conjoin clear top record originals entries edges before results after → RowsLaw entries edges before after) := by
  have leafCase : ∀ {target value before result after}, Leaf emptyGuard conjoin clear top record originals target value before result after →
      NodeLaw (.editAt target) value before after := by
    intro target value before result after step captured ready available _ heap
    have member : target ∈ record.paths := by simpa only [Allowed, All] using captured
    exact SourceEqualityAnnotationTarget.leaf annotation emptyValid conjoinedValid topValid step ready known originalClosed member available heap
  have emptyCase : ∀ {entries state}, NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) state state := by
    intro entries state _ _ _ _ heap; exact heap
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap entry depth free},
      EditRows emptyGuard conjoin clear top record originals entries edges before rebuilt middle →
      run (makeNode rebuilt) middle.native.machine.heap = (value, heap) → RowsLaw entries edges before middle →
      NodeLaw (.editBelow entries) (.node entry edges depth free) before (advanceHeap middle heap) := by
    intro entries edges before rebuilt middle value heap entry depth free _ built rowsIH captured ready available closed annotations
    have facts := ready.native.semantic.ready.semantic.1.normal.facts
    have middleHeap := rowsIH captured ready
      (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident)
      (MergedColdReaderClosed.node_children_closed _ facts entry edges depth free available closed) annotations
    change Heap annotation heap
    simpa only [built] using SourceEqualityAnnotationHeap.run annotation _ (SourceEqualityAnnotationHeap.makeNode annotation rebuilt) middle.native.machine.heap middleHeap
  have recursiveCase : ∀ {entries original before exposed heap result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap →
      EditNode emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap) result after →
      NodeLaw (.editBelow entries) exposed (advanceHeap before heap) after → NodeLaw (.editBelow entries) original before after := by
    intro entries original before exposed heap result after _ head _ ih captured ready available closed annotations
    have first := head.verified ready.native.semantic.ready available closed
    have semantic := SourceEqualityRequiredSemanticCache.head head ready.native.semantic available closed
    exact ih captured (ready.heap heap first.1 semantic) first.2.1 first.2.2.1
      (SourceEqualityAnnotationHead.head annotation head ready.native.semantic.ready available closed annotations)
  have nilChildren : ∀ {entries state}, ChildrenLaw entries ([] : List (Value Symbol Guard)) state state := by
    intro entries state _ _ _ _ heap; exact heap
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none → EditChildren emptyGuard conjoin clear top record originals entries (index + 1) values before results after →
      ChildrenLaw entries values before after → ChildrenLaw entries (value :: values) before after := by
    intro entries values before results after value index _ _ ih captured ready available closed heap
    exact ih captured ready (fun child member => available child (List.mem_cons_of_mem _ member))
      (fun child member => closed child (List.mem_cons_of_mem _ member)) heap
  have selectedCase : ∀ {entries edits value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some edits → EditNode emptyGuard conjoin clear top record originals edits value before result middle →
      EditChildren emptyGuard conjoin clear top record originals entries (index + 1) values middle results after →
      NodeLaw edits value before middle → ChildrenLaw entries values middle after → ChildrenLaw entries (value :: values) before after := by
    intro entries edits value before result middle values results after index found firstTrace _ firstIH restIH captured ready available closed heap
    have childCaptured : Allowed record edits := by
      have all := captured
      rw [Allowed, All] at all
      exact all (index : Int) edits (SourceEqualityNeededMap.lookup_mem _ _ _ found)
    have first := SourceEqualitySharedEditEffects.node emptyGuard conjoin clear top record originals base known originalClosed firstTrace
      childCaptured ready (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
    have firstHeap := firstIH childCaptured ready (available _ List.mem_cons_self) (closed _ List.mem_cons_self) heap
    exact restIH captured first.1
      (fun child member => first.2.1.available child (available child (List.mem_cons_of_mem _ member)))
      (fun child member => closed child (List.mem_cons_of_mem _ member)) firstHeap
  have nilRows : ∀ {entries state}, RowsLaw entries ([] : List (EdgeValue Symbol Guard)) state state := by
    intro entries state _ _ _ _ heap; exact heap
  have consCase : ∀ {entries before values middle result heap edges results after edge},
      EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap = (result, heap) →
      EditRows emptyGuard conjoin clear top record originals entries edges (advanceHeap middle heap) results after → ChildrenLaw entries edge.children before middle →
      RowsLaw entries edges (advanceHeap middle heap) after → RowsLaw entries (edge :: edges) before after := by
    intro entries before values middle result heap edges results after edge childTrace built _ childIH restIH captured ready resident closed annotations
    have facts := ready.native.semantic.ready.semantic.1.normal.facts
    have children := SourceEqualitySharedEditEffects.children emptyGuard conjoin clear top record originals base known originalClosed childTrace
      captured ready (facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)) (closed edge List.mem_cons_self)
    have middleHeap := childIH captured ready (facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)) (closed edge List.mem_cons_self) annotations
    have rebuilt := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      children.1.native.semantic.ready children.2.2.1
    have semantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      children.1.native.semantic children.2.2.1
    have edgeKeeps : Keeps middle.native.machine.heap heap := by simpa only [built] using rebuilt.1
    have heapSemantic : SemanticReady heap := by simpa only [built] using semantic
    have firstKeeps := children.2.1.trans edgeKeeps
    have emitted := SourceEqualityAnnotationHeap.run annotation _
      (SourceEqualityAnnotationHeap.makeEdge annotation edge.entry.key.symbol edge.entry.key.constraint values
        (annotations edge.entry.key edge (resident edge List.mem_cons_self))) middle.native.machine.heap middleHeap
    have afterHeap : Heap annotation heap := by simpa only [built] using emitted
    exact restIH captured (children.1.heap heap edgeKeeps heapSemantic)
      (fun original member => InternedEdgeResidency.edge_grows before.native.machine.heap heap firstKeeps.growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => closed original (List.mem_cons_of_mem _ member)) afterHeap
  refine ⟨?_, ?_, ?_⟩
  · intro edits value before result after trace
    exact EditNode.rec (motive_1 := fun edits value before _ after _ => NodeLaw edits value before after)
      (motive_2 := fun entries _ values before _ after _ => ChildrenLaw entries values before after)
      (motive_3 := fun entries edges before _ after _ => RowsLaw entries edges before after)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase trace
  · intro entries index values before results after trace
    exact EditChildren.rec (motive_1 := fun edits value before _ after _ => NodeLaw edits value before after)
      (motive_2 := fun entries _ values before _ after _ => ChildrenLaw entries values before after)
      (motive_3 := fun entries edges before _ after _ => RowsLaw entries edges before after)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase trace
  · intro entries edges before results after trace
    exact EditRows.rec (motive_1 := fun edits value before _ after _ => NodeLaw edits value before after)
      (motive_2 := fun entries _ values before _ after _ => ChildrenLaw entries values before after)
      (motive_3 := fun entries edges before _ after _ => RowsLaw entries edges before after)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase trace

/-- Complete shared node edits preserve annotations in the actual returned native heap. -/
theorem node {edits value before result after}
    (trace : EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result after) : NodeLaw edits value before after :=
  (all_preserved annotation emptyGuard conjoin clear top record originals base known originalClosed emptyValid conjoinedValid topValid).1 _ _ _ _ _ trace

/-- Complete shared child scans preserve annotations through their actual ordered requests. -/
theorem children {entries index values before results after}
    (trace : EditChildren (width := width) emptyGuard conjoin clear top record originals entries index values before results after) : ChildrenLaw entries values before after :=
  (all_preserved annotation emptyGuard conjoin clear top record originals base known originalClosed emptyValid conjoinedValid topValid).2.1 _ _ _ _ _ _ trace

/-- Complete shared row scans retain every original guard in the actual returned annotation heap. -/
theorem rows {entries edges before results after}
    (trace : EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before results after) : RowsLaw entries edges before after :=
  (all_preserved annotation emptyGuard conjoin clear top record originals base known originalClosed emptyValid conjoinedValid topValid).2.2 _ _ _ _ _ trace

/-- Child-list leaf and below-edit branches preserve annotations without changing shared target scope. -/
theorem list {edits values before results after}
    (trace : EditList (width := width) emptyGuard conjoin clear top record originals edits values before results after)
    (allowed : Allowed record edits) (ready : Ready emptyGuard conjoin clear top record originals base before)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values) (heap : Heap annotation before.native.machine.heap) : Heap annotation after.native.machine.heap := by
  cases trace with
  | leaf => exact heap
  | children actual => exact children annotation emptyGuard conjoin clear top record originals base known originalClosed emptyValid conjoinedValid topValid actual allowed ready available closed heap

end MicroCFTA.SourceEqualityAnnotationSharedEdit
