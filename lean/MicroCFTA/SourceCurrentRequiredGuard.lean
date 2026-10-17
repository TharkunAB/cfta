import MicroCFTA.SourceCurrentConstrainedCapProjectionGuard
import MicroCFTA.SourceCurrentRequiredQueryMemos

/-!
# Causal guard observations through actual Required reads

The actual successful graphs retain the guard heap at their exact return.
Unselected values can remain open and can have arbitrary guards.
These lemmas verify supplied graphs. They do not assume finite caps.
-/
namespace MicroCFTA.SourceCurrentRequiredGuard
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

private def NodeResult (valid : Guard → Prop) (value : Value Symbol Guard)
    (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Available before value → GuardHeap valid before → GuardHeap valid after
private def ChildrenResult (valid : Guard → Prop) (values : List (Value Symbol Guard))
    (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Values before values → GuardHeap valid before → GuardHeap valid after
private def RowsResult (valid : Guard → Prop) (edges : List (EdgeValue Symbol Guard))
    (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Edges before edges → GuardHeap valid before → GuardHeap valid after

private theorem all_required [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) :
    (∀ needed (value : Value Symbol Guard) before result after, RequireNode needed value before result after → NodeResult valid value before after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) before results after, RequireChildren entries index values before results after → ChildrenResult valid values before after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after, RequireRows entries edges before results after → RowsResult valid edges before after) := by
  have identityCase : ∀ {value : Value Symbol Guard} {state}, NodeResult valid value state state := by
    intro value state _ _ _ stored
    exact stored
  have emptyCase : ∀ {entries : List (Int × SourceEqualityNeeded.Needed)} {state : State Symbol Guard},
      entries ≠ [] → NodeResult valid .empty state state := by
    intro entries state _
    exact identityCase
  have ordinaryCase : ∀ {entries edges before rebuilt middle result after entry depth free},
      entries ≠ [] → RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before rebuilt middle →
      run (makeNode rebuilt) middle = (result, after) → RowsResult valid edges before middle →
      NodeResult valid (.node entry edges depth free) before after := by
    intro entries edges before rebuilt middle result after entry depth free _ _ built ih semantic _ available stored
    have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have retained := SourceCurrentConstrainedCapGuardHeap.preserve valid middle
      (run (makeNode rebuilt) middle).2 (ih semantic ‹CostHeap before› resident stored)
      (InternedShallowHeap.makeNode_noNewMu rebuilt middle)
    simpa only [built] using retained
  have recursiveCase : ∀ {entries original before exposed middle result after}, entries ≠ [] → Recursive original →
      SourceEqualityRequiredHead.Head original before exposed middle → RequireNode (Symbol := Symbol) (Guard := Guard) (.node entries) exposed middle result after →
      NodeResult valid exposed middle after → NodeResult valid original before after := by
    intro entries original before exposed middle result after _ _ head _ ih semantic costs available stored
    have effects := SourceCurrentRequiredHeapEffects.head (fun _ => True) head semantic costs (by intro _ _ _; trivial) available
    exact ih effects.2.1 effects.2.2.1 effects.2.2.2.2
      (SourceCurrentConstrainedCapProjectionGuard.head valid head semantic costs available stored)
  have nilChildren : ∀ {state : State Symbol Guard}, ChildrenResult valid [] state state := by
    intro state _ _ _ stored
    exact stored
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values before results after →
      ChildrenResult valid values before after → ChildrenResult valid (value :: values) before after := by
    intro entries values before results after value index _ _ ih semantic costs available stored
    exact ih semantic costs (fun child member => available child (List.mem_cons_of_mem _ member)) stored
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some needed →
      RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result middle →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values middle results after →
      NodeResult valid value before middle → ChildrenResult valid values middle after →
      ChildrenResult valid (value :: values) before after := by
    intro entries needed value before result middle values results after index _ first _ firstIH restIH semantic costs available stored
    have effects := SourceCurrentRequiredHeapEffects.node (fun _ => True) first semantic costs
      (by intro _ _ _; trivial) (available _ List.mem_cons_self)
    exact restIH effects.2.1 effects.2.2.1
      (fun child member => effects.1.available child (available child (List.mem_cons_of_mem _ member)))
      (firstIH semantic costs (available _ List.mem_cons_self) stored)
  have nilRows : ∀ {state : State Symbol Guard}, RowsResult valid [] state state := by
    intro state _ _ _ stored
    exact stored
  have rejectedCase : ∀ {entries edges before results after edge}, SourceEqualityNeeded.fits (.node entries) edge.children.length = false →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after → RowsResult valid edges before after →
      RowsResult valid (edge :: edges) before after := by
    intro entries edges before results after edge _ _ ih semantic costs resident stored
    exact ih semantic costs (fun original member => resident original (List.mem_cons_of_mem _ member)) stored
  have keptCase : ∀ {entries before values middle result afterEdge edges results after edge},
      SourceEqualityNeeded.fits (.node entries) edge.children.length = true →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges afterEdge results after →
      ChildrenResult valid edge.children before middle → RowsResult valid edges afterEdge after →
      RowsResult valid (edge :: edges) before after := by
    intro entries before values middle result afterEdge edges results after edge _ children built _ childIH restIH semantic costs resident stored
    have available : Values before edge.children := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
    have middleStored := childIH semantic costs available stored
    have effects := SourceCurrentRequiredHeapEffects.children (fun _ => True) children semantic costs (by intro _ _ _; trivial) available
    have edgeStored : GuardHeap valid afterEdge := by
      have unchanged : GuardHeap valid (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 := middleStored
      simpa only [built] using unchanged
    have constructor := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle effects.2.1.ready effects.2.2.2.2
    have afterKept : Keeps middle afterEdge := by simpa only [built] using constructor.1
    have afterSemantic : SemanticReady afterEdge := by
      simpa only [built] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle effects.2.1 effects.2.2.2.2
    have afterCosts : CostHeap afterEdge := by
      have same : CostHeap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 := effects.2.2.1
      simpa only [built] using same
    exact restIH afterSemantic afterCosts
      (fun original member => InternedEdgeResidency.edge_grows before afterEdge (effects.1.trans afterKept).growth original
        (resident original (List.mem_cons_of_mem _ member))) edgeStored
  refine ⟨?_, ?_, ?_⟩
  · intro needed value before result after actual
    exact RequireNode.rec (motive_1 := fun _ value before _ after _ => NodeResult valid value before after)
      (motive_2 := fun _ _ values before _ after _ => ChildrenResult valid values before after)
      (motive_3 := fun _ edges before _ after _ => RowsResult valid edges before after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries index values before results after actual
    exact RequireChildren.rec (motive_1 := fun _ value before _ after _ => NodeResult valid value before after)
      (motive_2 := fun _ _ values before _ after _ => ChildrenResult valid values before after)
      (motive_3 := fun _ edges before _ after _ => RowsResult valid edges before after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries edges before results after actual
    exact RequireRows.rec (motive_1 := fun _ value before _ after _ => NodeResult valid value before after)
      (motive_2 := fun _ _ values before _ after _ => ChildrenResult valid values before after)
      (motive_3 := fun _ edges before _ after _ => RowsResult valid edges before after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual

/-- The actual required node retains causal guard observations. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {needed : SourceEqualityNeeded.Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (stored : GuardHeap valid before) : GuardHeap valid after :=
  (all_required valid).1 _ _ _ _ _ actual semantic costs available stored

/-- The actual ordered child calls retain causal guard observations. -/
theorem children [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {entries : List (Int × SourceEqualityNeeded.Needed)} {index : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries index values before results after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (stored : GuardHeap valid before) : GuardHeap valid after :=
  (all_required valid).2.1 _ _ _ _ _ _ actual semantic costs available stored

/-- The actual kept and rejected rows retain causal guard observations. -/
theorem rows [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {entries : List (Int × SourceEqualityNeeded.Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireRows entries edges before results after) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (stored : GuardHeap valid before) : GuardHeap valid after :=
  (all_required valid).2.2 _ _ _ _ _ actual semantic costs resident stored

local notation "CurrentSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "CurrentGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- The same current requireAll reads retain guards and the literal forest length. -/
theorem requireAll [DecidableEq (EdgeKey CurrentSymbol CurrentGuard)] (valid : CurrentGuard → Prop) {paths : List (List Int)}
    {values results : List (Value CurrentSymbol CurrentGuard)} {before after : State CurrentSymbol CurrentGuard}
    {memos saved : EndpointMemoGateTrace.Memos}
    (reads : SourceCurrentRequiredQueryMemos.RequireAllReads paths values results before after memos saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (stored : GuardHeap valid before) : GuardHeap valid after ∧ results.length = values.length := by
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [SourceCurrentRequiredQueryMemos.RequireAllReads, compiled] at reads
      obtain ⟨actual, _reads⟩ := reads
      exact ⟨children valid actual semantic costs available stored, actual.length⟩

end MicroCFTA.SourceCurrentRequiredGuard
