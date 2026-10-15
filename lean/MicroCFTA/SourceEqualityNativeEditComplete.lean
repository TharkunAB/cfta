import MicroCFTA.SourceEqualityNativeEditEffects
import MicroCFTA.SourceEqualityNativeEditRanges

/-!
# Finite scoped simultaneous native edits

Actual-prefix word checks and local warm native progress derive every leaf.
Finite control, complete head reads, and actual constructors derive the
remaining graph. No completed callback or edit-worker execution is supplied.
-/
namespace MicroCFTA.SourceEqualityNativeEditComplete
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityEdits SourceEqualityNativeEditGraph SourceEqualityNativeEditRanges SourceEqualityNativeEditEffects

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (base : InternedConstructorTemplates.State Symbol Guard)

private def NodeComplete (edits : Edits (Value Symbol Guard)) (value : Value Symbol Guard) (before : NativeState width Symbol Guard) : Prop :=
  Captured base edits → Keeps base before.machine.heap → IdleReady emptyGuard conjoin before → Available before.machine.heap value → value.free = [] →
    ∃ result after, EditNode emptyGuard conjoin edits value before result after

private def ChildrenComplete (entries : List (Int × Edits (Value Symbol Guard))) (index : Nat)
    (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) : Prop :=
  Captured base (.editBelow entries) → Keeps base before.machine.heap → IdleReady emptyGuard conjoin before →
    Values before.machine.heap values → ClosedValues values → ∃ results after, EditChildren emptyGuard conjoin entries index values before results after

private def RowsComplete (entries : List (Int × Edits (Value Symbol Guard))) (edges : List (EdgeValue Symbol Guard))
    (before : NativeState width Symbol Guard) : Prop :=
  Captured base (.editBelow entries) → Keeps base before.machine.heap → IdleReady emptyGuard conjoin before →
    Edges before.machine.heap edges → ClosedEdges edges → ∃ results after, EditRows emptyGuard conjoin entries edges before results after

local notation "NodeLaw" => NodeComplete (width := width) emptyGuard conjoin base
local notation "ChildrenLaw" => ChildrenComplete (width := width) emptyGuard conjoin base
local notation "RowsLaw" => RowsComplete (width := width) emptyGuard conjoin base

private theorem complete :
    (∀ edits (value : Value Symbol Guard) (before : NativeState width Symbol Guard), NodeRanges emptyGuard conjoin edits value before → NodeLaw edits value before) ∧
    (∀ entries index (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard),
      ChildrenRanges emptyGuard conjoin entries index values before → ChildrenLaw entries index values before) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) (before : NativeState width Symbol Guard),
      RowsRanges emptyGuard conjoin entries edges before → RowsLaw entries edges before) := by
  have leafCase : ∀ {target value before}, SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, value⟩ .pure) before → NodeLaw (.editAt target) value before := by
    intro target value before ranges captured retained ready available closed
    have known : Available base target ∧ target.free = [] := by simpa only [Captured, All] using captured
    obtain ⟨result, after, step, _⟩ := SourceEqualityNativeScoped.complete emptyGuard conjoin before ready target value
      (retained.available target known.1) available known.2 closed ranges (fun _ _ => true) (by intros; rfl)
    exact ⟨result, after, .leaf step⟩
  have emptyCase : ∀ {entries before}, NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) before := by
    intro _ _ _ _ _ _ _
    exact ⟨_, _, .empty⟩
  have ordinaryCase : ∀ {entries edges before entry depth free}, RowsRanges emptyGuard conjoin entries edges before → RowsLaw entries edges before →
      NodeLaw (.editBelow entries) (.node entry edges depth free) before := by
    intro entries edges before entry depth free _ ih captured retained ready available closed
    have facts := ready.semantic.ready.semantic.1.normal.facts
    obtain ⟨rebuilt, middle, rows⟩ := ih captured retained ready (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident)
      (MergedColdReaderClosed.node_children_closed _ facts entry edges depth free available closed)
    exact ⟨_, _, .ordinary rows rfl⟩
  have recursiveCase : ∀ {original entries before}, SourceEqualityRequiredGraph.Recursive original →
      (∀ exposed heap, SourceEqualityRequiredHead.Head original before.machine.heap exposed heap → NodeRanges emptyGuard conjoin (.editBelow entries) exposed (advanceHeap before heap)) →
      (∀ exposed heap, SourceEqualityRequiredHead.Head original before.machine.heap exposed heap → NodeLaw (.editBelow entries) exposed (advanceHeap before heap)) →
      NodeLaw (.editBelow entries) original before := by
    intro original entries before recursive _ ih captured retained ready available closed
    obtain ⟨exposed, heap, head, keeps, resident, headClosed, _⟩ := SourceEqualityRequiredHead.complete _ _ ready.semantic.ready available closed
    obtain ⟨result, after, body⟩ := ih exposed heap head captured (retained.trans keeps)
      (ready.advance heap keeps (SourceEqualityRequiredSemanticCache.head head ready.semantic available closed)) resident headClosed
    exact ⟨result, after, .recursive recursive head body⟩
  have nilChildren : ∀ {entries index before}, ChildrenLaw entries index ([] : List (Value Symbol Guard)) before := by
    intro _ _ _ _ _ _ _ _
    exact ⟨_, _, .nil⟩
  have unselectedCase : ∀ {entries values before value} (index : Nat), SourceEqualityNeededMap.lookup (index : Int) entries = none →
      ChildrenRanges emptyGuard conjoin entries (index + 1) values before → ChildrenLaw entries (index + 1) values before →
      ChildrenLaw entries index (value :: values) before := by
    intro entries values before value index absent _ ih captured retained ready available closed
    obtain ⟨results, after, rest⟩ := ih captured retained ready
      (fun child member => available child (List.mem_cons_of_mem _ member)) (fun child member => closed child (List.mem_cons_of_mem _ member))
    exact ⟨_, _, .unselected index absent rest⟩
  have selectedCase : ∀ {entries edits value before values} (index : Nat), SourceEqualityNeededMap.lookup (index : Int) entries = some edits →
      NodeRanges emptyGuard conjoin edits value before →
      (∀ result middle, EditNode emptyGuard conjoin edits value before result middle → ChildrenRanges emptyGuard conjoin entries (index + 1) values middle) →
      NodeLaw edits value before →
      (∀ result middle, EditNode emptyGuard conjoin edits value before result middle → ChildrenLaw entries (index + 1) values middle) →
      ChildrenLaw entries index (value :: values) before := by
    intro entries edits value before values index found _ _ firstIH restIH captured retained ready available closed
    have childCaptured : Captured base edits := by
      have all := captured
      rw [Captured, All] at all
      exact all (index : Int) edits (SourceEqualityNeededMap.lookup_mem _ _ _ found)
    obtain ⟨result, middle, first⟩ := firstIH childCaptured retained ready (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
    have effects := SourceEqualityNativeEditEffects.node emptyGuard conjoin base first childCaptured retained ready
      (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
    obtain ⟨results, after, rest⟩ := restIH result middle first captured (retained.trans effects.2.1) effects.1
      (fun child member => effects.2.1.available child (available child (List.mem_cons_of_mem _ member)))
      (fun child member => closed child (List.mem_cons_of_mem _ member))
    exact ⟨_, _, .selected index found first rest⟩
  have nilRows : ∀ {entries before}, RowsLaw entries ([] : List (EdgeValue Symbol Guard)) before := by
    intro _ _ _ _ _ _ _
    exact ⟨_, _, .nil⟩
  have consCase : ∀ {entries edge edges before}, ChildrenRanges emptyGuard conjoin entries 0 edge.children before →
      (∀ values middle, EditChildren emptyGuard conjoin entries 0 edge.children before values middle → RowsRanges emptyGuard conjoin entries edges
        (advanceHeap middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.machine.heap).2)) →
      ChildrenLaw entries 0 edge.children before →
      (∀ values middle, EditChildren emptyGuard conjoin entries 0 edge.children before values middle → RowsLaw entries edges
        (advanceHeap middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.machine.heap).2)) →
      RowsLaw entries (edge :: edges) before := by
    intro entries edge edges before _ _ childrenIH restIH captured retained ready resident closed
    have available := ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
    obtain ⟨values, middle, children⟩ := childrenIH captured retained ready available (closed edge List.mem_cons_self)
    have effects := SourceEqualityNativeEditEffects.children emptyGuard conjoin base children captured retained ready available (closed edge List.mem_cons_self)
    let built := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.machine.heap
    have edgeKeeps := (SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.machine.heap effects.1.semantic.ready effects.2.2.1).1
    have edgeSemantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.machine.heap effects.1.semantic effects.2.2.1
    have firstKeeps := effects.2.1.trans edgeKeeps
    obtain ⟨results, after, rest⟩ := restIH values middle children captured (retained.trans firstKeeps)
      (effects.1.advance built.2 edgeKeeps edgeSemantic)
      (fun original member => InternedEdgeResidency.edge_grows before.machine.heap built.2 firstKeeps.growth original (resident original (List.mem_cons_of_mem _ member)))
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
theorem node {edits value before} (ranges : NodeRanges (width := width) emptyGuard conjoin edits value before)
    (captured : Captured base edits) (retained : Keeps base before.machine.heap) (ready : IdleReady emptyGuard conjoin before)
    (available : Available before.machine.heap value) (closed : value.free = []) :
    ∃ result after, EditNode emptyGuard conjoin edits value before result after ∧ IdleReady emptyGuard conjoin after ∧
      Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] := by
  obtain ⟨result, after, trace⟩ := (complete emptyGuard conjoin base).1 _ _ _ ranges captured retained ready available closed
  exact ⟨result, after, trace, SourceEqualityNativeEditEffects.node emptyGuard conjoin base trace captured retained ready available closed⟩

/-- Actual-prefix word checks derive finite complete native source child-list edits. -/
theorem list {edits values before} (ranges : ListRanges (width := width) emptyGuard conjoin edits values before)
    (captured : Captured base edits) (retained : Keeps base before.machine.heap) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) :
    ∃ results after, EditList emptyGuard conjoin edits values before results after ∧ IdleReady emptyGuard conjoin after ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results := by
  cases edits with
  | editAt target => exact ⟨values, before, .leaf, ready, pure_keeps _ ready.semantic.ready, available, closed⟩
  | editBelow entries =>
      obtain ⟨results, after, trace⟩ := (complete emptyGuard conjoin base).2.1 entries 0 values before ranges captured retained ready available closed
      exact ⟨results, after, .children trace, SourceEqualityNativeEditEffects.children emptyGuard conjoin base trace captured retained ready available closed⟩

end MicroCFTA.SourceEqualityNativeEditComplete
