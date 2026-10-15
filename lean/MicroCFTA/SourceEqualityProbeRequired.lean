import MicroCFTA.SourceEqualityRequiredSemanticEffects
import MicroCFTA.SourceEqualityProbeHead
import MicroCFTA.SourceEqualityRequiredListFacts

/-!
# Filtered Mu probes through the complete required-path graph

The graph induction uses actual head and constructor preservation. Existing
execution uniqueness supplies every intermediate available or resident input.
No final probe invariant is supplied.
-/
namespace MicroCFTA.SourceEqualityProbeRequired
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredGraph
open SourceEqualityRequiredSemanticCache SourceEqualityRequiredListFacts
open InternedFreshOrdinaryProbeHeap (Heap)

private def NodePreserved (value : Value Symbol Guard) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → Available before value → value.free = [] → Heap before → Heap after

private def ChildrenPreserved (values : List (Value Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → Values before values → ClosedValues values → Heap before → Heap after

private def RowsPreserved (edges : List (EdgeValue Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → Edges before edges → ClosedEdges edges → Heap before → Heap after

private theorem all_preserved [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ needed (value : Value Symbol Guard) before result after,
      RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result after → NodePreserved (Symbol := Symbol) (Guard := Guard) value before after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) before results after,
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries index values before results after → ChildrenPreserved (Symbol := Symbol) (Guard := Guard) values before after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after → RowsPreserved (Symbol := Symbol) (Guard := Guard) edges before after) := by
  have identityCase : ∀ {value : Value Symbol Guard} {state}, NodePreserved (Symbol := Symbol) (Guard := Guard) value state state := by
    intro value state _ _ _ heap; exact heap
  have emptyCase : ∀ {entries : List (Int × Needed)} {state}, entries ≠ [] → NodePreserved (Symbol := Symbol) (Guard := Guard) (.empty : Value Symbol Guard) state state := by
    intro entries state _ _ _ _ heap; exact heap
  have ordinaryCase : ∀ {entries edges before rebuilt middle result after entry depth free},
      entries ≠ [] → RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before rebuilt middle → run (makeNode rebuilt) middle = (result, after) →
      RowsPreserved (Symbol := Symbol) (Guard := Guard) edges before middle → NodePreserved (Symbol := Symbol) (Guard := Guard) (.node entry edges depth free) before after := by
    intro entries edges before rebuilt middle result after entry depth free _ trace rebuiltEq rowsIH semantic available closed heap
    have facts := semantic.ready.semantic.1.normal.facts
    have resident : Edges before edges := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
    have closedEdges := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
    have middleHeap := rowsIH semantic resident closedEdges heap
    simpa only [rebuiltEq] using InternedFreshOrdinaryProbeHeap.node rebuilt middle middleHeap
  have recursiveCase : ∀ {entries original before exposed middle result after},
      entries ≠ [] → Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      RequireNode (Symbol := Symbol) (Guard := Guard) (.node entries) exposed middle result after → NodePreserved (Symbol := Symbol) (Guard := Guard) exposed middle after → NodePreserved (Symbol := Symbol) (Guard := Guard) original before after := by
    intro entries original before exposed middle result after _ _ trace _ bodyIH semantic available closed heap
    have nextSemantic := SourceEqualityRequiredSemanticCache.head trace semantic available closed
    have checked := trace.verified semantic.ready available closed
    exact bodyIH nextSemantic checked.2.1 checked.2.2.1 (SourceEqualityProbeHead.head trace semantic.ready available closed heap)
  have nilChildren : ∀ {state}, ChildrenPreserved (Symbol := Symbol) (Guard := Guard) ([] : List (Value Symbol Guard)) state state := by
    intro state _ _ _ heap; exact heap
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none → RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values before results after →
      ChildrenPreserved (Symbol := Symbol) (Guard := Guard) values before after → ChildrenPreserved (Symbol := Symbol) (Guard := Guard) (value :: values) before after := by
    intro entries values before results after value index _ _ restIH semantic available closed heap
    exact restIH semantic (fun child member => available child (List.mem_cons_of_mem _ member))
      (fun child member => closed child (List.mem_cons_of_mem _ member)) heap
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some needed → RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result middle →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values middle results after → NodePreserved (Symbol := Symbol) (Guard := Guard) value before middle →
      ChildrenPreserved (Symbol := Symbol) (Guard := Guard) values middle after → ChildrenPreserved (Symbol := Symbol) (Guard := Guard) (value :: values) before after := by
    intro entries needed value before result middle values results after index _ first _ firstIH restIH semantic available closed heap
    have firstAvailable := available value List.mem_cons_self
    have firstClosed := closed value List.mem_cons_self
    have nextSemantic := SourceEqualityRequiredSemanticEffects.node first semantic firstAvailable firstClosed
    have nextHeap := firstIH semantic firstAvailable firstClosed heap
    have checked := SourceEqualityRequiredExecution.node_verified first semantic.ready firstAvailable firstClosed
    exact restIH nextSemantic (fun child member => checked.1.available child (available child (List.mem_cons_of_mem _ member)))
      (fun child member => closed child (List.mem_cons_of_mem _ member)) nextHeap
  have nilRows : ∀ {state}, RowsPreserved (Symbol := Symbol) (Guard := Guard) ([] : List (EdgeValue Symbol Guard)) state state := by
    intro state _ _ _ heap; exact heap
  have rejectedCase : ∀ {entries edges before results after edge},
      fits (.node entries) edge.children.length = false → RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after →
      RowsPreserved (Symbol := Symbol) (Guard := Guard) edges before after → RowsPreserved (Symbol := Symbol) (Guard := Guard) (edge :: edges) before after := by
    intro entries edges before results after edge _ _ restIH semantic resident closed heap
    exact restIH semantic (fun original member => resident original (List.mem_cons_of_mem _ member))
      (fun original member => closed original (List.mem_cons_of_mem _ member)) heap
  have keptCase : ∀ {entries before values middle result afterEdge edges results after edge},
      fits (.node entries) edge.children.length = true → RequireChildren (Symbol := Symbol) (Guard := Guard) entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges afterEdge results after → ChildrenPreserved (Symbol := Symbol) (Guard := Guard) edge.children before middle →
      RowsPreserved (Symbol := Symbol) (Guard := Guard) edges afterEdge after → RowsPreserved (Symbol := Symbol) (Guard := Guard) (edge :: edges) before after := by
    intro entries before values middle result afterEdge edges results after edge _ childTrace rebuilt _ childIH restIH semantic resident closed heap
    have facts := semantic.ready.semantic.1.normal.facts
    have available : Values before edge.children := facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
    have middleSemantic := SourceEqualityRequiredSemanticEffects.children childTrace semantic available (closed edge List.mem_cons_self)
    have middleHeap := childIH semantic available (closed edge List.mem_cons_self) heap
    have checked := children_verified childTrace semantic.ready available (closed edge List.mem_cons_self)
    have edgeSemantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle middleSemantic checked.2.1
    have edgeChecked := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle middleSemantic.ready checked.2.1
    have afterSemantic : SemanticReady afterEdge := by simpa only [rebuilt] using edgeSemantic
    have edgeKeeps : Keeps middle afterEdge := by simpa only [rebuilt] using edgeChecked.1
    have growth := (checked.1.trans edgeKeeps).growth
    have emitted := InternedFreshOrdinaryProbeHeap.edge edge.entry.key.symbol edge.entry.key.constraint values middle middleHeap
    have afterHeap : Heap afterEdge := by simpa only [rebuilt] using emitted
    exact restIH afterSemantic
      (fun original member => InternedEdgeResidency.edge_grows before afterEdge growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => closed original (List.mem_cons_of_mem _ member)) afterHeap
  refine ⟨?_, ?_, ?_⟩
  · intro needed value before result after trace
    exact RequireNode.rec
      (motive_1 := fun _ value before _ after _ => NodePreserved (Symbol := Symbol) (Guard := Guard) value before after)
      (motive_2 := fun _ _ values before _ after _ => ChildrenPreserved (Symbol := Symbol) (Guard := Guard) values before after)
      (motive_3 := fun _ edges before _ after _ => RowsPreserved (Symbol := Symbol) (Guard := Guard) edges before after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace
  · intro entries index values before results after trace
    exact RequireChildren.rec
      (motive_1 := fun _ value before _ after _ => NodePreserved (Symbol := Symbol) (Guard := Guard) value before after)
      (motive_2 := fun _ _ values before _ after _ => ChildrenPreserved (Symbol := Symbol) (Guard := Guard) values before after)
      (motive_3 := fun _ edges before _ after _ => RowsPreserved (Symbol := Symbol) (Guard := Guard) edges before after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace
  · intro entries edges before results after trace
    exact RequireRows.rec
      (motive_1 := fun _ value before _ after _ => NodePreserved (Symbol := Symbol) (Guard := Guard) value before after)
      (motive_2 := fun _ _ values before _ after _ => ChildrenPreserved (Symbol := Symbol) (Guard := Guard) values before after)
      (motive_3 := fun _ edges before _ after _ => RowsPreserved (Symbol := Symbol) (Guard := Guard) edges before after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace

/-- Every completed required-node graph retains the probe invariant. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)]
    {needed : Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result after) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (heap : Heap before) : Heap after :=
  (all_preserved).1 needed value before result after trace semantic available closed heap

/-- Every completed child graph retains the probe invariant. -/
theorem children [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireChildren (Symbol := Symbol) (Guard := Guard) entries index values before results after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) (heap : Heap before) : Heap after :=
  (all_preserved).2.1 entries index values before results after trace semantic available closed heap

/-- Every completed row graph retains the probe invariant. -/
theorem rows [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (heap : Heap before) : Heap after :=
  (all_preserved).2.2 entries edges before results after trace semantic resident closed heap

end MicroCFTA.SourceEqualityProbeRequired
