import MicroCFTA.SourceCurrentConstrainedCapRequired
import MicroCFTA.SourceCurrentConstrainedCapPathExposure
import MicroCFTA.SourceCurrentHereditaryRequiredMerge
import MicroCFTA.SourceEqualityProjectionLanguage

/-!
# Original path masks through actual Required calls

The cap controls every visited branch. The separate mask can select one
position. Actual Required calls retain every supported original path and
the causal Mu store. Ordered child relations retain the original positions.
These results require completed graphs. They do not assert completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapRequiredSupport
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceEqualityAnnotationLanguage SourceEqualityProjectionGraph
open SourceCurrentConstrainedCap (Cap Edge)
open SourceCurrentConstrainedCapPaths (Supported ForestSupported)
open SourceCurrentConstrainedCapPathExposure (Row)
open SourceCurrentHereditaryConstruction (MuStored)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- Every supported path of one original value remains supported by its actual replacement. -/
def Preserves (valid : Guard → Prop) (original result : Value Symbol Guard) : Prop :=
  ∀ path, Supported valid path original → Supported valid path result

private theorem selected {valid : Guard → Prop} {originals results : List (Value Symbol Guard)}
    (related : Language.All₂ (Preserves valid) originals results) (index : Int) (path : List Int)
    (supported : ∀ original, select originals index = some original → Supported valid path original) :
    ∀ result, select results index = some result → Supported valid path result := by
  intro result found
  obtain ⟨original, earlier, retained⟩ := SourceEqualityProjectionLanguage.all₂_signed related index result found
  exact retained path (supported original earlier)

private def NodeResult (valid : Guard → Prop) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (_after : State Symbol Guard) : Prop :=
  ∀ depth, SemanticReady before → CostHeap before → Available before value → value.free = [] → MuStored valid before →
    Cap valid depth value → Preserves valid value result

private def ChildrenResult (valid : Guard → Prop) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (results : List (Value Symbol Guard)) (_after : State Symbol Guard) : Prop :=
  ∀ depth, SemanticReady before → CostHeap before → Values before values → ClosedValues values → MuStored valid before →
    (∀ value ∈ values, Cap valid depth value) → Language.All₂ (Preserves valid) values results

private def RowsResult (valid : Guard → Prop) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (EdgeValue Symbol Guard)) (_after : State Symbol Guard) : Prop :=
  ∀ depth, SemanticReady before → CostHeap before → Edges before edges → ClosedEdges edges → MuStored valid before →
    (∀ edge ∈ edges, Edge valid depth edge) → ∀ index path,
      (∀ edge ∈ edges, Row valid index path edge) → ∀ edge ∈ results, Row valid index path edge

private theorem all_required [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) :
    (∀ needed (value : Value Symbol Guard) before result after, RequireNode needed value before result after → NodeResult valid value before result after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) before results after, RequireChildren entries index values before results after → ChildrenResult valid values before results after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after, RequireRows entries edges before results after → RowsResult valid edges before results after) := by
  have identityCase : ∀ {value : Value Symbol Guard} {state}, NodeResult valid value state value state := by
    intro value state depth _ _ _ _ _ _ path supported
    exact supported
  have emptyCase : ∀ {entries : List (Int × SourceEqualityNeeded.Needed)} {state : State Symbol Guard},
      entries ≠ [] → NodeResult valid .empty state .empty state := by
    intro entries state _
    exact identityCase
  have ordinaryCase : ∀ {entries edges before rebuilt middle result after entry level free},
      entries ≠ [] → RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before rebuilt middle →
      run (makeNode rebuilt) middle = (result, after) → RowsResult valid edges before rebuilt middle →
      NodeResult valid (.node entry edges level free) before result after := by
    intro entries edges before rebuilt middle result after entry level free nonempty rows built ih depth semantic costs available closed stored bounded path supported
    cases path with
    | nil =>
        have localResult := SourceCurrentHereditaryRequiredMerge.node valid (.ordinary nonempty rows built)
          semantic costs available closed stored supported.root
        exact .plain [] localResult.2
    | cons index path =>
        have facts := semantic.ready.semantic.1.normal.facts
        have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
        have rowClosed := MergedColdReaderClosed.node_children_closed before facts entry edges level free available closed
        have retained := ih depth semantic costs resident rowClosed stored
          (fun edge member => SourceCurrentConstrainedCap.node_edge bounded edge member) index path
          (fun edge member => supported.node_selected edge member)
        have effects := SourceCurrentRequiredHeapEffects.rows (fun _ => True) rows semantic costs (by intro _ _ _; trivial) resident
        simpa only [built] using SourceCurrentConstrainedCapPathExposure.makeNode valid index path rebuilt middle
          effects.2.1.ready.semantic.1.normal.facts.coherent effects.2.1.ready.semantic.1.normal.facts.linked effects.2.2.2.2 retained
  have recursiveCase : ∀ {entries original before exposed middle result after}, entries ≠ [] → Recursive original →
      SourceEqualityRequiredHead.Head original before exposed middle → RequireNode (Symbol := Symbol) (Guard := Guard) (.node entries) exposed middle result after →
      NodeResult valid exposed middle result after → NodeResult valid original before result after := by
    intro entries original before exposed middle result after nonempty recursive head body ih depth semantic costs available closed stored bounded path supported
    cases path with
    | nil =>
        have localResult := SourceCurrentHereditaryRequiredMerge.node valid (.recursive nonempty recursive head body)
          semantic costs available closed stored supported.root
        exact .plain [] localResult.2
    | cons index path =>
        have headCap := SourceCurrentConstrainedCapExposure.head valid depth head semantic.ready available closed bounded stored
        have headMask := SourceCurrentConstrainedCapPathExposure.head valid index path head semantic.ready available closed supported stored
        have effects := SourceCurrentRequiredHeapEffects.head (fun _ => True) head semantic costs (by intro _ _ _; trivial) available
        exact ih depth effects.2.1 effects.2.2.1 effects.2.2.2.2 (head.verified semantic.ready available closed).2.2.1
          headCap.1 headCap.2 (index :: path) headMask.2
  have nilChildren : ∀ {state : State Symbol Guard}, ChildrenResult valid [] state [] state := by
    intro state depth _ _ _ _ _ _
    exact .nil
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values before results after →
      ChildrenResult valid values before results after → ChildrenResult valid (value :: values) before (value :: results) after := by
    intro entries values before results after value index _ _ ih depth semantic costs available closed stored bounded
    exact .cons (fun _ supported => supported) (ih depth semantic costs
      (fun child member => available child (List.mem_cons_of_mem _ member))
      (fun child member => closed child (List.mem_cons_of_mem _ member)) stored
      (fun child member => bounded child (List.mem_cons_of_mem _ member)))
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some needed →
      RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result middle →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values middle results after →
      NodeResult valid value before result middle → ChildrenResult valid values middle results after →
      ChildrenResult valid (value :: values) before (result :: results) after := by
    intro entries needed value before result middle values results after index _ first _ firstIH restIH depth semantic costs available closed stored bounded
    have firstMask := firstIH depth semantic costs (available _ List.mem_cons_self) (closed _ List.mem_cons_self) stored (bounded _ List.mem_cons_self)
    have firstCap := SourceCurrentConstrainedCapRequired.node valid depth first semantic costs
      (available _ List.mem_cons_self) (closed _ List.mem_cons_self) stored (bounded _ List.mem_cons_self)
    have effects := SourceCurrentRequiredHeapEffects.node (fun _ => True) first semantic costs (by intro _ _ _; trivial) (available _ List.mem_cons_self)
    exact .cons firstMask (restIH depth effects.2.1 effects.2.2.1
      (fun child member => effects.1.available child (available child (List.mem_cons_of_mem _ member)))
      (fun child member => closed child (List.mem_cons_of_mem _ member)) firstCap.1
      (fun child member => bounded child (List.mem_cons_of_mem _ member)))
  have nilRows : ∀ {state : State Symbol Guard}, RowsResult valid [] state [] state := by
    intro state depth _ _ _ _ _ _ index path _ edge member
    cases member
  have rejectedCase : ∀ {entries edges before results after edge}, SourceEqualityNeeded.fits (.node entries) edge.children.length = false →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after → RowsResult valid edges before results after →
      RowsResult valid (edge :: edges) before results after := by
    intro entries edges before results after edge _ _ ih depth semantic costs resident closed stored bounded index path supported
    exact ih depth semantic costs (fun original member => resident original (List.mem_cons_of_mem _ member))
      (fun original member => closed original (List.mem_cons_of_mem _ member)) stored
      (fun original member => bounded original (List.mem_cons_of_mem _ member)) index path
      (fun original member => supported original (List.mem_cons_of_mem _ member))
  have keptCase : ∀ {entries before values middle result afterEdge edges results after edge},
      SourceEqualityNeeded.fits (.node entries) edge.children.length = true →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges afterEdge results after →
      ChildrenResult valid edge.children before values middle → RowsResult valid edges afterEdge results after →
      RowsResult valid (edge :: edges) before (result :: results) after := by
    intro entries before values middle result afterEdge edges results after edge _ children built _ childIH restIH depth semantic costs resident closed stored bounded index path supported
    have original := bounded edge List.mem_cons_self
    have available : Values before edge.children := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
    have childCaps : ∀ child ∈ edge.children, Cap valid (depth - 1) child := by
      cases depth with
      | zero => exact fun child member => Cap.plain 0 (original.2 child member)
      | succ depth => exact original
    have related := childIH (depth - 1) semantic costs available (closed edge List.mem_cons_self) stored childCaps
    have middleCaps := SourceCurrentConstrainedCapRequired.children valid (depth - 1) children semantic costs available
      (closed edge List.mem_cons_self) stored childCaps
    have effects := SourceCurrentRequiredHeapEffects.children (fun _ => True) children semantic costs (by intro _ _ _; trivial) available
    have edgeStored : MuStored valid afterEdge := by simpa only [built] using middleCaps.1.makeEdge edge.entry.key.symbol edge.entry.key.constraint values
    have constructor := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle effects.2.1.ready effects.2.2.2.2
    have afterKept : Keeps middle afterEdge := by simpa only [built] using constructor.1
    have afterSemantic : SemanticReady afterEdge := by
      simpa only [built] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle effects.2.1 effects.2.2.2.2
    have afterCosts : CostHeap afterEdge := by
      have same : CostHeap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 := effects.2.2.1
      simpa only [built] using same
    have tail := restIH depth afterSemantic afterCosts
      (fun original member => InternedEdgeResidency.edge_grows before afterEdge (effects.1.trans afterKept).growth original
        (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => closed original (List.mem_cons_of_mem _ member)) edgeStored
      (fun original member => bounded original (List.mem_cons_of_mem _ member)) index path
      (fun original member => supported original (List.mem_cons_of_mem _ member))
    intro output member
    rcases List.mem_cons.mp member with rfl | member
    · have same : output.children = values := by simpa only [built] using constructor.2.2
      intro child found
      rw [same] at found
      exact selected related index path (supported edge List.mem_cons_self) child found
    · exact tail output member
  refine ⟨?_, ?_, ?_⟩
  · intro needed value before result after actual
    exact RequireNode.rec (motive_1 := fun _ value before result after _ => NodeResult valid value before result after)
      (motive_2 := fun _ _ values before results after _ => ChildrenResult valid values before results after)
      (motive_3 := fun _ edges before results after _ => RowsResult valid edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries index values before results after actual
    exact RequireChildren.rec (motive_1 := fun _ value before result after _ => NodeResult valid value before result after)
      (motive_2 := fun _ _ values before results after _ => ChildrenResult valid values before results after)
      (motive_3 := fun _ edges before results after _ => RowsResult valid edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries edges before results after actual
    exact RequireRows.rec (motive_1 := fun _ value before result after _ => NodeResult valid value before result after)
      (motive_2 := fun _ _ values before results after _ => ChildrenResult valid values before results after)
      (motive_3 := fun _ edges before results after _ => RowsResult valid edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual

/-- Actual Required retains every original supported path and the causal Mu store. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat)
    {needed : SourceEqualityNeeded.Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (closed : value.free = []) (stored : MuStored valid before) (bounded : Cap valid depth value) :
    MuStored valid after ∧ Preserves valid value result :=
  ⟨(SourceCurrentConstrainedCapRequired.node valid depth actual semantic costs available closed stored bounded).1,
    (all_required valid).1 _ _ _ _ _ actual depth semantic costs available closed stored bounded⟩

/-- Ordered child calls retain all path masks at their original positions. -/
theorem children [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat)
    {entries : List (Int × SourceEqualityNeeded.Needed)} {index : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries index values before results after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (bounded : ∀ value ∈ values, Cap valid depth value) :
    MuStored valid after ∧ Language.All₂ (Preserves valid) values results :=
  ⟨(SourceCurrentConstrainedCapRequired.children valid depth actual semantic costs available closed stored bounded).1,
    (all_required valid).2.1 _ _ _ _ _ _ actual depth semantic costs available closed stored bounded⟩

/-- Rejected rows disappear; every kept row retains each original selected-child mask. -/
theorem rows [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (depth : Nat)
    {entries : List (Int × SourceEqualityNeeded.Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireRows entries edges before results after) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (stored : MuStored valid before)
    (bounded : ∀ edge ∈ edges, Edge valid depth edge) :
    MuStored valid after ∧ ∀ index path,
      (∀ edge ∈ edges, Row valid index path edge) → ∀ edge ∈ results, Row valid index path edge :=
  ⟨(SourceCurrentConstrainedCapRequired.rows valid depth actual semantic costs resident closed stored bounded).1,
    (all_required valid).2.2 _ _ _ _ _ actual depth semantic costs resident closed stored bounded⟩

/-- The ordered conditional relation retains the distinct forest-root and signed-slot masks. -/
theorem forest_supported (valid : Guard → Prop) {values results : List (Value Symbol Guard)}
    (related : Language.All₂ (Preserves valid) values results) (path : List Int)
    (supported : ForestSupported valid path values) : ForestSupported valid path results := by
  cases path with
  | nil =>
      intro result member
      have all : ∀ value ∈ values, Supported valid [] value := fun value member => .plain [] (supported value member)
      induction related with
      | nil => cases member
      | @cons value output values outputs first rest ih =>
          rcases List.mem_cons.mp member with rfl | member
          · exact (first [] (all value List.mem_cons_self)).root
          · exact ih (fun child present => supported child (List.mem_cons_of_mem _ present)) member
              (fun child present => all child (List.mem_cons_of_mem _ present))
  | cons index path => exact selected related index path supported

local notation "CurrentSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "CurrentGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Current requireAll reads retain the same ordered conditional relation at their actual return. -/
theorem requireAll [DecidableEq (EdgeKey CurrentSymbol CurrentGuard)] (valid : CurrentGuard → Prop) (depth : Nat)
    {paths : List (List Int)} {values results : List (Value CurrentSymbol CurrentGuard)} {before after : State CurrentSymbol CurrentGuard}
    {memos saved : EndpointMemoGateTrace.Memos}
    (reads : SourceCurrentRequiredQueryMemos.RequireAllReads paths values results before after memos saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values) (closed : ClosedValues values)
    (stored : MuStored valid before) (bounded : ∀ value ∈ values, Cap valid depth value) :
    MuStored valid after ∧ Language.All₂ (Preserves valid) values results := by
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [SourceCurrentRequiredQueryMemos.RequireAllReads, compiled] at reads
      obtain ⟨actual, _reads⟩ := reads
      exact children valid depth actual semantic costs available closed stored bounded

end MicroCFTA.SourceCurrentConstrainedCapRequiredSupport
