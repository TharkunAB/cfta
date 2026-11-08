import MicroCFTA.SourceCurrentHereditaryRequiredMerge
import MicroCFTA.SourceSynthesisAnnotationFieldConstructors
import MicroCFTA.MergedPhysicalGroupEdges

/-!
# Annotated Program fields through annotation-only Required calls

Only position zero can have a required child request. Every later position
follows the actual unselected branch and retains its literal value. Row
reconstruction retains the original guard. The proof does not annotate
Program guards or unrelated Program siblings. These are completed-run laws.
-/
namespace MicroCFTA.SourceCurrentHereditaryProgramRequired
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceEqualityNeeded (Needed)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceSynthesisTypePathRoles (AnnotationFields)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- The actual child lookup is absent at each position after the first. -/
def AnnotationOnly (entries : List (Int × Needed)) : Prop :=
  ∀ index : Nat, index ≠ 0 → SourceEqualityNeededMap.lookup (index : Int) entries = none

/-- An existing first child is an annotated Type. -/
def FirstField (valid : Guard → Prop) (values : List (Value Symbol Guard)) : Prop :=
  ∀ value, values[0]? = some value → Annotated valid value

private theorem tail_identity [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard}
    (actual : RequireChildren entries index values before results after)
    (only : AnnotationOnly entries) (positive : 0 < index) : results = values ∧ after = before := by
  cases actual with
  | nil => exact ⟨rfl, rfl⟩
  | unselected offset absent rest =>
      obtain ⟨rfl, rfl⟩ := tail_identity rest only (by omega)
      exact ⟨rfl, rfl⟩
  | selected offset found first rest =>
      rw [only index (by omega)] at found
      cases found
termination_by values.length

/-- Actual child-zero recursion retains its Type and leaves all later children unchanged. -/
theorem children [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {entries : List (Int × Needed)} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries 0 values before results after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (typed : FirstField valid values) (only : AnnotationOnly entries) :
    MuStored valid after ∧ FirstField valid results ∧ results.tail = values.tail := by
  cases values with
  | nil =>
      cases actual
      exact ⟨stored, typed, rfl⟩
  | cons value values =>
      cases actual with
      | unselected offset absent rest =>
          obtain ⟨rfl, rfl⟩ := tail_identity rest only (by omega)
          exact ⟨stored, typed, rfl⟩
      | selected offset found first rest =>
          have own := SourceCurrentHereditaryRequiredMerge.node valid first semantic costs
            (available _ List.mem_cons_self) (closed _ List.mem_cons_self) stored (typed value rfl)
          obtain ⟨rfl, rfl⟩ := tail_identity rest only (by omega)
          refine ⟨own.1, ?_, rfl⟩
          intro child selected
          cases Option.some.inj selected
          exact own.2

private theorem edge_rebuilt [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {symbol : Symbol} {guard : Guard} {values : List (Value Symbol Guard)}
    {before after : State Symbol Guard} {result : EdgeValue Symbol Guard}
    (actual : run (makeEdge symbol guard values) before = (result, after))
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (stored : MuStored valid before) (typed : FirstField valid values) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧
      MuStored valid after ∧ FirstField valid result.children := by
  have checked := SourceEqualityRequiredCache.edge symbol guard values before semantic.ready available
  have ready := SourceEqualityRequiredSemanticCache.edge symbol guard values before semantic available
  have finalCosts : CostHeap (run (makeEdge symbol guard values) before).2 := costs
  have fields := MergedPhysicalGroupEdges.makeEdge_fields before semantic.ready.semantic.1.normal.facts
    symbol guard values available
  have same : result.children = values := by simpa only [actual] using fields.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [actual] using checked.1
  · simpa only [actual] using ready
  · simpa only [actual] using finalCosts
  · simpa only [actual] using stored.makeEdge symbol guard values
  · rw [same]; exact typed

/-- Actual ordered row work retains each surviving first field and the completed Mu store. -/
theorem rows [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireRows entries edges before results after) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (stored : MuStored valid before)
    (typed : ∀ edge ∈ edges, FirstField valid edge.children) (only : AnnotationOnly entries) :
    MuStored valid after ∧ ∀ edge ∈ results, FirstField valid edge.children := by
  cases edges with
  | nil =>
      cases actual
      exact ⟨stored, by intro edge member; cases member⟩
  | cons edge edges =>
      cases actual with
      | rejected doesNotFit rest =>
          exact rows valid rest semantic costs
            (fun edge member => resident edge (List.mem_cons_of_mem _ member))
            (fun edge member => closed edge (List.mem_cons_of_mem _ member)) stored
            (fun edge member => typed edge (List.mem_cons_of_mem _ member)) only
      | kept doesFit adjusted made rest =>
          have facts := semantic.ready.semantic.1.normal.facts
          have available : Values before edge.children := facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
          have own := children valid adjusted semantic costs available (closed edge List.mem_cons_self)
            stored (typed edge List.mem_cons_self) only
          have physical := SourceCurrentRequiredHeapEffects.children (fun _ => True) adjusted semantic costs
            (by intro _ _ _; trivial) available
          have rebuilt := edge_rebuilt valid made physical.2.1 physical.2.2.1 physical.2.2.2.2 own.1 own.2.1
          have growth := physical.1.trans rebuilt.1
          have later := rows valid rest rebuilt.2.1 rebuilt.2.2.1
            (fun edge member => InternedEdgeResidency.edge_grows _ _ growth.growth edge
              (resident edge (List.mem_cons_of_mem _ member)))
            (fun edge member => closed edge (List.mem_cons_of_mem _ member)) rebuilt.2.2.2.1
            (fun edge member => typed edge (List.mem_cons_of_mem _ member)) only
          refine ⟨later.1, ?_⟩
          intro result member
          rcases List.mem_cons.mp member with rfl | tail
          · exact rebuilt.2.2.2.2
          · exact later.2 result tail
termination_by edges.length

private theorem node_rebuilt [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {edges : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (actual : run (makeNode edges) before = (result, after)) (facts : InternedNestedFacts.Facts before)
    (resident : Edges before edges) (stored : MuStored valid before)
    (typed : ∀ edge ∈ edges, FirstField valid edge.children) :
    MuStored valid after ∧ AnnotationFields valid result := by
  constructor
  · simpa only [actual] using stored.makeNode edges
  · simpa only [actual] using
      SourceSynthesisAnnotationFieldConstructors.makeNode_fields valid edges before facts resident typed

/-- An annotation-only Program request retains its ordinary first-field certificate. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {entries : List (Int × Needed)} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode (.node entries) value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (closed : value.free = []) (stored : MuStored valid before) (fields : AnnotationFields valid value)
    (only : AnnotationOnly entries) : MuStored valid after ∧ AnnotationFields valid result := by
  cases fields with
  | empty =>
      cases actual with
      | identity | empty => exact ⟨stored, .empty⟩
      | recursive nonempty recursive head body => cases recursive
  | node entry edges depth free typed =>
      cases actual with
      | identity => exact ⟨stored, .node entry edges depth free typed⟩
      | ordinary nonempty projected made =>
          have facts := semantic.ready.semantic.1.normal.facts
          have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
          have rowClosed := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
          have localRows := rows valid projected semantic costs resident rowClosed stored typed only
          have physical := SourceCurrentRequiredHeapEffects.rows (fun _ => True) projected semantic costs
            (by intro _ _ _; trivial) resident
          exact node_rebuilt valid made physical.2.1.ready.semantic.1.normal.facts physical.2.2.2.2 localRows.1 localRows.2
      | recursive nonempty recursive head body => cases recursive

end MicroCFTA.SourceCurrentHereditaryProgramRequired
