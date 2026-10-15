import MicroCFTA.SourceEqualitySharedEditEffects
import MicroCFTA.SourceEqualitySharedEditRanges

/-!
# Finite simultaneous edits with shared class target closures

Actual-prefix checks derive first force and every native leaf. Shared
receipts retain original scope through all later rows and recursive heads.
No completed callback, target, or edit-worker execution is supplied.
-/
namespace MicroCFTA.SourceEqualitySharedEditComplete
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualitySharedTargetState
open SourceEqualityEdits SourceEqualitySharedEditGraph SourceEqualitySharedEditRanges SourceEqualitySharedEditEffects

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard)
variable (known : Values base originals) (originalClosed : ClosedValues originals)

private def NodeComplete (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard) (before : SharedState width Symbol Guard) : Prop :=
  Allowed record edits → Ready emptyGuard conjoin clear top record originals base before → Available before.native.machine.heap value → value.free = [] →
    ∃ result after, EditNode emptyGuard conjoin clear top record originals edits value before result after

private def ChildrenComplete (entries : List (Int × Edits EqualityNormalize.Path)) (index : Nat)
    (values : List (Value Symbol Guard)) (before : SharedState width Symbol Guard) : Prop :=
  Allowed record (.editBelow entries) → Ready emptyGuard conjoin clear top record originals base before →
    Values before.native.machine.heap values → ClosedValues values → ∃ results after, EditChildren emptyGuard conjoin clear top record originals entries index values before results after

private def RowsComplete (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard))
    (before : SharedState width Symbol Guard) : Prop :=
  Allowed record (.editBelow entries) → Ready emptyGuard conjoin clear top record originals base before →
    Edges before.native.machine.heap edges → ClosedEdges edges → ∃ results after, EditRows emptyGuard conjoin clear top record originals entries edges before results after

local notation "NodeLaw" => NodeComplete (width := width) emptyGuard conjoin clear top record originals base
local notation "ChildrenLaw" => ChildrenComplete (width := width) emptyGuard conjoin clear top record originals base
local notation "RowsLaw" => RowsComplete (width := width) emptyGuard conjoin clear top record originals base

include known originalClosed

private theorem complete :
    (∀ edits (value : Value Symbol Guard) (before : SharedState width Symbol Guard), NodeRanges emptyGuard conjoin clear top record originals edits value before → NodeLaw edits value before) ∧
    (∀ entries index (values : List (Value Symbol Guard)) (before : SharedState width Symbol Guard),
      ChildrenRanges emptyGuard conjoin clear top record originals entries index values before → ChildrenLaw entries index values before) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) (before : SharedState width Symbol Guard),
      RowsRanges emptyGuard conjoin clear top record originals entries edges before → RowsLaw entries edges before) := by
  have leafCase : ∀ {target value before}, SourceEqualitySharedTargetLeafComplete.LeafRanges emptyGuard conjoin clear top record originals target value before → NodeLaw (.editAt target) value before := by
    intro target value before ranges allowed ready available closed
    have member : target ∈ record.paths := by simpa only [Allowed, All] using allowed
    obtain ⟨result, after, step, _⟩ := SourceEqualitySharedTargetLeafComplete.complete emptyGuard conjoin clear top record originals base
      known originalClosed target member value before ready ranges available closed
    exact ⟨result, after, .leaf step⟩
  have emptyCase : ∀ {entries before}, NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) before := by
    intro _ _ _ _ _ _
    exact ⟨_, _, .empty⟩
  have ordinaryCase : ∀ {entries edges before entry depth free}, RowsRanges emptyGuard conjoin clear top record originals entries edges before → RowsLaw entries edges before →
      NodeLaw (.editBelow entries) (.node entry edges depth free) before := by
    intro entries edges before entry depth free _ ih captured ready available closed
    have facts := ready.native.semantic.ready.semantic.1.normal.facts
    obtain ⟨rebuilt, middle, rows⟩ := ih captured ready (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident)
      (MergedColdReaderClosed.node_children_closed _ facts entry edges depth free available closed)
    exact ⟨_, _, .ordinary rows rfl⟩
  have recursiveCase : ∀ {original entries before}, SourceEqualityRequiredGraph.Recursive original →
      (∀ exposed heap, SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap → NodeRanges emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap)) →
      (∀ exposed heap, SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap → NodeLaw (.editBelow entries) exposed (advanceHeap before heap)) →
      NodeLaw (.editBelow entries) original before := by
    intro original entries before recursive _ ih captured ready available closed
    obtain ⟨exposed, heap, head, keeps, resident, headClosed, _⟩ := SourceEqualityRequiredHead.complete _ _ ready.native.semantic.ready available closed
    obtain ⟨result, after, body⟩ := ih exposed heap head captured
      (ready.heap heap keeps (SourceEqualityRequiredSemanticCache.head head ready.native.semantic available closed)) resident headClosed
    exact ⟨result, after, .recursive recursive head body⟩
  have nilChildren : ∀ {entries index before}, ChildrenLaw entries index ([] : List (Value Symbol Guard)) before := by
    intro _ _ _ _ _ _ _
    exact ⟨_, _, .nil⟩
  have unselectedCase : ∀ {entries values before value} (index : Nat), SourceEqualityNeededMap.lookup (index : Int) entries = none →
      ChildrenRanges emptyGuard conjoin clear top record originals entries (index + 1) values before → ChildrenLaw entries (index + 1) values before →
      ChildrenLaw entries index (value :: values) before := by
    intro entries values before value index absent _ ih captured ready available closed
    obtain ⟨results, after, rest⟩ := ih captured ready
      (fun child member => available child (List.mem_cons_of_mem _ member)) (fun child member => closed child (List.mem_cons_of_mem _ member))
    exact ⟨_, _, .unselected index absent rest⟩
  have selectedCase : ∀ {entries edits value before values} (index : Nat), SourceEqualityNeededMap.lookup (index : Int) entries = some edits →
      NodeRanges emptyGuard conjoin clear top record originals edits value before →
      (∀ result middle, EditNode emptyGuard conjoin clear top record originals edits value before result middle → ChildrenRanges emptyGuard conjoin clear top record originals entries (index + 1) values middle) →
      NodeLaw edits value before →
      (∀ result middle, EditNode emptyGuard conjoin clear top record originals edits value before result middle → ChildrenLaw entries (index + 1) values middle) →
      ChildrenLaw entries index (value :: values) before := by
    intro entries edits value before values index found _ _ firstIH restIH captured ready available closed
    have childCaptured : Allowed record edits := by
      have all := captured
      rw [Allowed, All] at all
      exact all (index : Int) edits (SourceEqualityNeededMap.lookup_mem _ _ _ found)
    obtain ⟨result, middle, first⟩ := firstIH childCaptured ready (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
    have effects := SourceEqualitySharedEditEffects.node emptyGuard conjoin clear top record originals base known originalClosed first childCaptured ready
      (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
    obtain ⟨results, after, rest⟩ := restIH result middle first captured effects.1
      (fun child member => effects.2.1.available child (available child (List.mem_cons_of_mem _ member)))
      (fun child member => closed child (List.mem_cons_of_mem _ member))
    exact ⟨_, _, .selected index found first rest⟩
  have nilRows : ∀ {entries before}, RowsLaw entries ([] : List (EdgeValue Symbol Guard)) before := by
    intro _ _ _ _ _ _
    exact ⟨_, _, .nil⟩
  have consCase : ∀ {entries edge edges before}, ChildrenRanges emptyGuard conjoin clear top record originals entries 0 edge.children before →
      (∀ values middle, EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle → RowsRanges emptyGuard conjoin clear top record originals entries edges
        (advanceHeap middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap).2)) →
      ChildrenLaw entries 0 edge.children before →
      (∀ values middle, EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle → RowsLaw entries edges
        (advanceHeap middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap).2)) →
      RowsLaw entries (edge :: edges) before := by
    intro entries edge edges before _ _ childrenIH restIH captured ready resident closed
    have available := ready.native.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
    obtain ⟨values, middle, children⟩ := childrenIH captured ready available (closed edge List.mem_cons_self)
    have effects := SourceEqualitySharedEditEffects.children emptyGuard conjoin clear top record originals base known originalClosed children captured ready available (closed edge List.mem_cons_self)
    let built := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap
    have edgeKeeps := (SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap effects.1.native.semantic.ready effects.2.2.1).1
    have edgeSemantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap effects.1.native.semantic effects.2.2.1
    have firstKeeps := effects.2.1.trans edgeKeeps
    obtain ⟨results, after, rest⟩ := restIH values middle children captured
      (effects.1.heap built.2 edgeKeeps edgeSemantic)
      (fun original member => InternedEdgeResidency.edge_grows before.native.machine.heap built.2 firstKeeps.growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => closed original (List.mem_cons_of_mem _ member))
    exact ⟨_, _, .cons children rfl rest⟩
  refine ⟨?_, ?_, ?_⟩
  · intro edits value before ranges
    exact NodeRanges.rec (motive_1 := fun edits value before _ => NodeLaw edits value before)
      (motive_2 := fun entries index values before _ => ChildrenLaw entries index values before)
      (motive_3 := fun entries edges before _ => RowsLaw entries edges before)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase ranges
  · intro entries index values before ranges
    exact ChildrenRanges.rec (motive_1 := fun edits value before _ => NodeLaw edits value before)
      (motive_2 := fun entries index values before _ => ChildrenLaw entries index values before)
      (motive_3 := fun entries edges before _ => RowsLaw entries edges before)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase ranges
  · intro entries edges before ranges
    exact RowsRanges.rec (motive_1 := fun edits value before _ => NodeLaw edits value before)
      (motive_2 := fun entries index values before _ => ChildrenLaw entries index values before)
      (motive_3 := fun entries edges before _ => RowsLaw entries edges before)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase ranges

/-- Actual-prefix word checks derive finite complete native node edits and all final invariants. -/
theorem node {edits value before} (ranges : NodeRanges (width := width) emptyGuard conjoin clear top record originals edits value before)
    (captured : Allowed record edits) (ready : Ready emptyGuard conjoin clear top record originals base before)
    (available : Available before.native.machine.heap value) (closed : value.free = []) :
    ∃ result after, EditNode emptyGuard conjoin clear top record originals edits value before result after ∧ Ready emptyGuard conjoin clear top record originals base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Available after.native.machine.heap result ∧ result.free = [] := by
  obtain ⟨result, after, trace⟩ := (complete emptyGuard conjoin clear top record originals base known originalClosed).1 _ _ _ ranges captured ready available closed
  exact ⟨result, after, trace, SourceEqualitySharedEditEffects.node emptyGuard conjoin clear top record originals base known originalClosed trace captured ready available closed⟩

/-- Actual-prefix word checks derive finite complete native source child-list edits. -/
theorem list {edits values before} (ranges : ListRanges (width := width) emptyGuard conjoin clear top record originals edits values before)
    (captured : Allowed record edits) (ready : Ready emptyGuard conjoin clear top record originals base before)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values) :
    ∃ results after, EditList emptyGuard conjoin clear top record originals edits values before results after ∧ Ready emptyGuard conjoin clear top record originals base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Values after.native.machine.heap results ∧ ClosedValues results := by
  cases edits with
  | editAt target => exact ⟨values, before, .leaf, ready, pure_keeps _ ready.native.semantic.ready, available, closed⟩
  | editBelow entries =>
      obtain ⟨results, after, trace⟩ := (complete emptyGuard conjoin clear top record originals base known originalClosed).2.1 entries 0 values before ranges captured ready available closed
      exact ⟨results, after, .children trace, SourceEqualitySharedEditEffects.children emptyGuard conjoin clear top record originals base known originalClosed trace captured ready available closed⟩

end MicroCFTA.SourceEqualitySharedEditComplete
