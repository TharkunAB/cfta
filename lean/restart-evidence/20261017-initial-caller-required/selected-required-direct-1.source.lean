import MicroCFTA.SourceCurrentConstrainedCapOpenExposure
import MicroCFTA.SourceCurrentConstrainedCapProjectionGuard
import MicroCFTA.SourceCurrentRequiredQueryMemos

/-!
# Local caps and causal guard heaps through selected Required reads

Actual successful Required calls retain caps at their exact returned heap.
Empty requirements do not inspect references. Unselected siblings can stay
open. Recursive reads use actual source effects and causal Mu observations.
These results verify supplied graphs. They do not assert completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapSelectedRequired
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap (Cap Edge)
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

private def NodeResult (valid : Guard → Prop) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  ∀ capDepth, SemanticReady before → CostHeap before → Available before value → GuardHeap valid before → Cap valid capDepth value →
    GuardHeap valid after ∧ Cap valid capDepth result
private def ChildrenResult (valid : Guard → Prop) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (results : List (Value Symbol Guard)) (after : State Symbol Guard) : Prop :=
  ∀ capDepth, SemanticReady before → CostHeap before → Values before values → GuardHeap valid before →
    (∀ value ∈ values, Cap valid capDepth value) → GuardHeap valid after ∧ ∀ value ∈ results, Cap valid capDepth value
private def RowsResult (valid : Guard → Prop) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard) : Prop :=
  ∀ capDepth, SemanticReady before → CostHeap before → Edges before edges → GuardHeap valid before →
    (∀ edge ∈ edges, Edge valid capDepth edge) →
      GuardHeap valid after ∧ ∀ edge ∈ results, Edge valid capDepth edge

private theorem all_required [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) :
    (∀ needed (value : Value Symbol Guard) before result after, RequireNode needed value before result after → NodeResult valid value before result after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) before results after, RequireChildren entries index values before results after → ChildrenResult valid values before results after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after, RequireRows entries edges before results after → RowsResult valid edges before results after) := by
  have identityCase : ∀ {value : Value Symbol Guard} {state}, NodeResult valid value state value state := by
    intro value state capDepth _ _ _ stored annotated
    exact ⟨stored, annotated⟩
  have emptyCase : ∀ {entries : List (Int × SourceEqualityNeeded.Needed)} {state : State Symbol Guard},
      entries ≠ [] → NodeResult valid .empty state .empty state := by
    intro entries state _
    exact identityCase
  have ordinaryCase : ∀ {entries edges before rebuilt middle result after entry depth free},
      entries ≠ [] → RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before rebuilt middle →
      run (makeNode rebuilt) middle = (result, after) → RowsResult valid edges before rebuilt middle →
      NodeResult valid (.node entry edges depth free) before result after := by
    intro entries edges before rebuilt middle result after entry depth free _ rows built ih capDepth semantic costs available stored annotated
    have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    obtain ⟨middleStored, rebuiltAnnotations⟩ := ih capDepth semantic costs resident stored
      (fun edge member => SourceCurrentConstrainedCap.node_edge annotated edge member)
    have effects := SourceCurrentRequiredHeapEffects.rows (fun _ => True) rows semantic costs (by intro _ _ _; trivial) resident
    have produced := SourceCurrentConstrainedCap.makeNode valid capDepth rebuilt middle effects.2.1.ready.semantic.1.normal.facts.coherent
      effects.2.1.ready.semantic.1.normal.facts.linked effects.2.2.2.2 rebuiltAnnotations
    have retained := SourceCurrentConstrainedCapGuardHeap.preserve valid middle
      (run (makeNode rebuilt) middle).2 middleStored (InternedShallowHeap.makeNode_noNewMu rebuilt middle)
    exact ⟨by simpa only [built] using retained, by simpa only [built] using produced⟩
  have recursiveCase : ∀ {entries original before exposed middle result after}, entries ≠ [] → Recursive original →
      SourceEqualityRequiredHead.Head original before exposed middle → RequireNode (Symbol := Symbol) (Guard := Guard) (.node entries) exposed middle result after →
      NodeResult valid exposed middle result after → NodeResult valid original before result after := by
    intro entries original before exposed middle result after _ _ head _ ih capDepth semantic costs available stored annotated
    obtain ⟨_middleStored, exposedAnnotations⟩ := SourceCurrentConstrainedCapOpenExposure.head valid capDepth head semantic costs available annotated
      (SourceCurrentConstrainedCapGuardNative.stored valid before stored)
    have effects := SourceCurrentRequiredHeapEffects.head (fun _ => True) head semantic costs (by intro _ _ _; trivial) available
    have middleGuards := SourceCurrentConstrainedCapProjectionGuard.head valid head semantic costs available stored
    exact ih capDepth effects.2.1 effects.2.2.1 effects.2.2.2.2 middleGuards exposedAnnotations
  have nilChildren : ∀ {state : State Symbol Guard},
      ChildrenResult valid [] state [] state := by
    intro state capDepth _ _ _ stored _
    exact ⟨stored, fun _ impossible => nomatch impossible⟩
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values before results after →
      ChildrenResult valid values before results after → ChildrenResult valid (value :: values) before (value :: results) after := by
    intro entries values before results after value index _ _ ih capDepth semantic costs available stored annotated
    obtain ⟨finalStored, restAnnotations⟩ := ih capDepth semantic costs (fun child member => available child (List.mem_cons_of_mem _ member))
      stored (fun child member => annotated child (List.mem_cons_of_mem _ member))
    refine ⟨finalStored, ?_⟩
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact annotated _ List.mem_cons_self
    · exact restAnnotations child member
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some needed →
      RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result middle →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values middle results after →
      NodeResult valid value before result middle → ChildrenResult valid values middle results after →
      ChildrenResult valid (value :: values) before (result :: results) after := by
    intro entries needed value before result middle values results after index _ first _ firstIH restIH capDepth semantic costs available stored annotated
    obtain ⟨middleStored, firstAnnotations⟩ := firstIH capDepth semantic costs (available _ List.mem_cons_self) stored (annotated _ List.mem_cons_self)
    have effects := SourceCurrentRequiredHeapEffects.node (fun _ => True) first semantic costs (by intro _ _ _; trivial) (available _ List.mem_cons_self)
    obtain ⟨finalStored, restAnnotations⟩ := restIH capDepth effects.2.1 effects.2.2.1
      (fun child member => effects.1.available child (available child (List.mem_cons_of_mem _ member)))
      middleStored
      (fun child member => annotated child (List.mem_cons_of_mem _ member))
    refine ⟨finalStored, ?_⟩
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact firstAnnotations
    · exact restAnnotations child member
  have nilRows : ∀ {state : State Symbol Guard}, RowsResult valid [] state [] state := by
    intro state capDepth _ _ _ stored _
    exact ⟨stored, fun _ impossible => nomatch impossible⟩
  have rejectedCase : ∀ {entries edges before results after edge}, SourceEqualityNeeded.fits (.node entries) edge.children.length = false →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after → RowsResult valid edges before results after →
      RowsResult valid (edge :: edges) before results after := by
    intro entries edges before results after edge _ _ ih capDepth semantic costs resident stored annotated
    exact ih capDepth semantic costs (fun original member => resident original (List.mem_cons_of_mem _ member))
      stored
      (fun original member => annotated original (List.mem_cons_of_mem _ member))
  have keptCase : ∀ {entries before values middle result afterEdge edges results after edge},
      SourceEqualityNeeded.fits (.node entries) edge.children.length = true →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges afterEdge results after →
      ChildrenResult valid edge.children before values middle → RowsResult valid edges afterEdge results after →
      RowsResult valid (edge :: edges) before (result :: results) after := by
    intro entries before values middle result afterEdge edges results after edge _ children built _ childIH restIH capDepth semantic costs resident stored annotated
    have original := annotated edge List.mem_cons_self
    have available : Values before edge.children := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
    obtain ⟨middleStored, childAnnotations⟩  := childIH (capDepth - 1) semantic costs available stored (by
      cases capDepth with
      | zero => exact fun child member => Cap.plain 0 (original.2 child member)
      | succ depth => exact original)
    have effects := SourceCurrentRequiredHeapEffects.children (fun _ => True) children semantic costs (by intro _ _ _; trivial) available
    have edgeStored : GuardHeap valid afterEdge := by
      simpa only [built] using SourceCurrentConstrainedCapGuardHeap.preserve valid middle
        (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 middleStored
        (InternedShallowHeap.makeEdge_noNewMu edge.entry.key.symbol edge.entry.key.constraint values middle)
    have edgeAnnotations : Edge valid capDepth result := by
      simpa only [built] using SourceCurrentConstrainedCap.makeEdge valid capDepth edge.entry.key.symbol edge.entry.key.constraint values middle
        effects.2.1.ready.semantic.1.normal.facts.coherent effects.2.1.ready.semantic.1.normal.facts.cached effects.2.2.2.2
        (fun zero => by subst capDepth; exact original.1) childAnnotations
    have constructor := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle effects.2.1.ready effects.2.2.2.2
    have afterKept : Keeps middle afterEdge := by simpa only [built] using constructor.1
    have afterSemantic : SemanticReady afterEdge := by
      simpa only [built] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle effects.2.1 effects.2.2.2.2
    have afterCosts : CostHeap afterEdge := by
      have same : CostHeap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 := effects.2.2.1
      simpa only [built] using same
    obtain ⟨finalStored, restAnnotations⟩ := restIH capDepth afterSemantic afterCosts
      (fun original member => InternedEdgeResidency.edge_grows before afterEdge (effects.1.trans afterKept).growth original
        (resident original (List.mem_cons_of_mem _ member)))
      edgeStored
      (fun original member => annotated original (List.mem_cons_of_mem _ member))
    refine ⟨finalStored, ?_⟩
    intro output member
    rcases List.mem_cons.mp member with rfl | member
    · exact edgeAnnotations
    · exact restAnnotations output member
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

/-- The same actual required-node graph retains conditional Mu laws and local caps. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth : Nat)
    {needed : SourceEqualityNeeded.Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (stored : GuardHeap valid before) (annotated : Cap valid capDepth value) :
    GuardHeap valid after ∧ Cap valid capDepth result :=
  (all_required valid).1 _ _ _ _ _ actual capDepth semantic costs available stored annotated

/-- Existing ordered required-child calls retain each output cap at its actual position. -/
theorem children [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth : Nat)
    {entries : List (Int × SourceEqualityNeeded.Needed)} {index : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries index values before results after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (stored : GuardHeap valid before) (annotated : ∀ value ∈ values, Cap valid capDepth value) :
    GuardHeap valid after ∧ ∀ value ∈ results, Cap valid capDepth value :=
  (all_required valid).2.1 _ _ _ _ _ _ actual capDepth semantic costs available stored annotated

/-- Actual rejected rows disappear and retained rows keep their local guards and child caps. -/
theorem rows [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth : Nat)
    {entries : List (Int × SourceEqualityNeeded.Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireRows entries edges before results after) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (stored : GuardHeap valid before)
    (annotated : ∀ edge ∈ edges, Edge valid capDepth edge) :
    GuardHeap valid after ∧ ∀ edge ∈ results, Edge valid capDepth edge :=
  (all_required valid).2.2 _ _ _ _ _ actual capDepth semantic costs resident stored annotated

local notation "CurrentSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "CurrentGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Supplied current requireAll reads retain local caps at the same exact return. -/
theorem requireAll [DecidableEq (EdgeKey CurrentSymbol CurrentGuard)] (valid : CurrentGuard → Prop) (capDepth : Nat) {paths : List (List Int)}
    {values results : List (Value CurrentSymbol CurrentGuard)} {before after : State CurrentSymbol CurrentGuard}
    {memos saved : EndpointMemoGateTrace.Memos}
    (reads : SourceCurrentRequiredQueryMemos.RequireAllReads paths values results before after memos saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (stored : GuardHeap valid before) (annotated : ∀ value ∈ values, Cap valid capDepth value) :
    GuardHeap valid after ∧ (∀ value ∈ results, Cap valid capDepth value) ∧ results.length = values.length := by
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [SourceCurrentRequiredQueryMemos.RequireAllReads, compiled] at reads
      obtain ⟨actual, _reads⟩ := reads
      have returned := children valid capDepth actual semantic costs available stored annotated
      exact ⟨returned.1, returned.2, actual.length⟩

end MicroCFTA.SourceCurrentConstrainedCapSelectedRequired
