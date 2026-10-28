import MicroCFTA.SourceCurrentAllocatedProbeExposure
import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.InternedFreshOrdinaryStoredConstraintHeap
import MicroCFTA.SourceEqualityProjectionCosts
import MicroCFTA.SourcePruningEnumerationNativeQueryProjectionHeap
import MicroCFTA.SourceCurrentRequiredHeapEffects

/-!
# Projectability through actual open exposure and projection

This draft follows the actual recorded worker endpoints.
It does not assert completion of an arbitrary native prefix.
-/
namespace MicroCFTA.SourcePruningEnumerationParentProjectionPrimitives
open InternedConstructorTemplates InternedProbeProvenance
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
variable {Symbol : Type}

/-- Node allocation adds no edge guard. -/
theorem node_heap [DecidableEq (EdgeKey Symbol Guard)]
    (rows : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (heap : Heap before) : Heap (run (makeNode rows) before).2 :=
  SourceEqualityAnnotationHeap.run _ _ (SourceEqualityAnnotationHeap.makeNode _ rows) before heap

end MicroCFTA.SourcePruningEnumerationParentProjectionPrimitives

namespace MicroCFTA.SourcePruningEnumerationProbeExposureProjectionHeap
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
variable {Symbol : Type}

/-- A completed row read retains projectability for available open inputs. -/
theorem read_heap [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard}
    {rows : List (EdgeValue Symbol Guard)}
    (actual : SourceEqualityProjectionRead.Read value before rows after)
    (semantic : SemanticReady before) (available : Available before value)
    (heap : Heap before) : Heap after := by
  cases actual with
  | done fuel completed =>
      simpa only [completed, MergedSourceExposure.Result.state] using
        SourceCurrentOpenExposureFields.nodeEdges_heap
          (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
          fuel value before semantic heap available

/-- The actual head node adds no edge guard after its completed row read. -/
theorem head_heap [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (semantic : SemanticReady before) (available : Available before value)
    (heap : Heap before) : Heap after := by
  cases actual with
  | read fuel edges middle exposed rebuilt =>
      have middleHeap := read_heap (.done fuel exposed) semantic available heap
      simpa only [rebuilt] using
        SourcePruningEnumerationParentProjectionPrimitives.node_heap edges middle middleHeap

end MicroCFTA.SourcePruningEnumerationProbeExposureProjectionHeap

namespace MicroCFTA.SourcePruningEnumerationPathProjectionHeap
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead SourceEqualityProjectionUnion
variable {Symbol : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual ordered row read retains projectability at its complete returned heap. -/
theorem readAll_heap
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : ReadAll values before edges after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) (heap : Heap before) : Heap after := by
  induction actual with
  | nil => exact heap
  | @cons value before rows middle values more after first rest ih =>
      have reached := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      have current := SourcePruningEnumerationProbeExposureProjectionHeap.read_heap first
        semantic (available _ List.mem_cons_self) heap
      exact ih reached.2.1 reached.2.2.1
        (fun child member => reached.1.available child (available child (List.mem_cons_of_mem _ member))) current

/-- The literal source union reads its inputs and adds no new edge record afterward. -/
theorem union_heap
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (actual : Union values before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) (heap : Heap before) : Heap after := by
  cases actual with
  | node read built =>
      have current := readAll_heap read semantic costs available heap
      have sameState := congrArg Prod.snd built
      dsimp only at sameState
      rw [← sameState]
      exact SourcePruningEnumerationParentProjectionPrimitives.node_heap _ _ current

private def NodeHeap (value : Value Symbol Guard) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Available before value → Heap before → Heap after

private def RowsHeap (edges : List (EdgeValue Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Edges before edges → Heap before → Heap after

private theorem project_heaps :
    (∀ path (value : Value Symbol Guard) before result after,
      Project path value before result after → NodeHeap value before after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsHeap edges before after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeHeap value state state := by
    intro value state _ _ _ heap
    exact heap
  have emptyCase : ∀ {state}, NodeHeap (.empty : Value Symbol Guard) state state := by
    intro state _ _ _ heap
    exact heap
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) («Guard» := Guard) path index edges before values middle →
      Union values middle result after → RowsHeap edges before middle →
      NodeHeap (.node entry edges depth free) before after := by
    intro path index edges before values middle result after entry depth free rows union ih semantic costs available heap
    have resident := InternedEdgeResidency.resident_edges before
      semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have current := ih semantic costs resident heap
    have reached := SourceEqualityProjectionCosts.rows_effects rows semantic costs resident
    exact union_heap union reached.2.1 reached.2.2.1 reached.2.2.2 current
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) («Guard» := Guard) (index :: path) exposed middle result after →
      NodeHeap exposed middle after → NodeHeap original before after := by
    intro original before exposed middle path index result after _ head _ ih semantic costs available heap
    have reached := SourceEqualityProjectionCosts.head_effects head semantic costs available
    have current := SourcePruningEnumerationProbeExposureProjectionHeap.head_heap head
      semantic available heap
    exact ih reached.2.1 reached.2.2.1 reached.2.2.2 current
  have nilCase : ∀ {state}, RowsHeap ([] : List (EdgeValue Symbol Guard)) state state := by
    intro state _ _ _ heap
    exact heap
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) («Guard» := Guard) path index edges before results after →
      RowsHeap edges before after → RowsHeap (edge :: edges) before after := by
    intro edge path index edges before results after _ _ ih semantic costs resident heap
    exact ih semantic costs (fun row member => resident row (List.mem_cons_of_mem _ member)) heap
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) («Guard» := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeHeap child before middle →
      RowsHeap edges middle after → RowsHeap (edge :: edges) before after := by
    intro edge index child path before result middle edges results after found first _ firstIH restIH semantic costs resident heap
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
      (resident edge List.mem_cons_self) child (select_member found)
    have current := firstIH semantic costs available heap
    have reached := SourceEqualityProjectionCosts.project_effects first semantic costs available
    exact restIH reached.2.1 reached.2.2.1
      (fun row member => InternedEdgeResidency.edge_grows before middle reached.1.growth row
        (resident row (List.mem_cons_of_mem _ member))) current
  constructor
  · intro path value before result after trace
    exact Project.rec (motive_1 := fun _ value before _ after _ => NodeHeap value before after)
      (motive_2 := fun _ _ edges before _ after _ => RowsHeap edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace
  · intro path index edges before results after trace
    exact ProjectRows.rec (motive_1 := fun _ value before _ after _ => NodeHeap value before after)
      (motive_2 := fun _ _ edges before _ after _ => RowsHeap edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace

/-- Every completed actual path projection retains the entire projectability heap. -/
theorem project_heap
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project path value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (heap : Heap before) : Heap after :=
  project_heaps.1 _ _ _ _ _ actual semantic costs available heap

/-- Ordered actual row projections retain every old and newly reconstructed edge record. -/
theorem rows_heap
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)} {results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (actual : ProjectRows path index edges before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges)
    (heap : Heap before) : Heap after := project_heaps.2 _ _ _ _ _ _ actual semantic costs resident heap

/-- The actual forest root, missing child and selected child branches preserve projectability. -/
theorem forest_heap
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Forest path values before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) (heap : Heap before) : Heap after := by
  cases actual with
  | root union => exact union_heap union semantic costs available heap
  | missing => exact heap
  | selected found body => exact project_heap body semantic costs (available _ (select_member found)) heap

end MicroCFTA.SourcePruningEnumerationPathProjectionHeap
