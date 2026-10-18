import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceEqualityProjectionCosts

/-!
# Physical fields through completed open projection

Actual head reads preserve the annotation heap. Ordered projections retain
it at each returned child scope. The final source union reads every operand
and constructs one node without a new guard.
No complete projection or future output invariant is supplied as a premise.
-/
namespace MicroCFTA.SourceCurrentOpenProjectionFields
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open SourceEqualityAnnotationHeap (Heap)

/-- An actual row read preserves annotations in its returned cache. -/
theorem read (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : SourceEqualityProjectionRead.Read value before edges after) (semantic : SemanticReady before)
    (available : Available before value) (heap : Heap annotation before) : Heap annotation after := by
  cases trace with
  | done fuel completed =>
      simpa only [completed, MergedSourceExposure.Result.state] using
        SourceCurrentOpenExposureFields.nodeEdges_heap annotation fuel value before semantic heap available

/-- Ordered union operands preserve annotations through all actual row reads. -/
theorem readAll (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : SourceEqualityProjectionUnion.ReadAll values before edges after) (semantic : SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before) (available : Values before values) (heap : Heap annotation before) : Heap annotation after := by
  induction trace with
  | nil => exact heap
  | cons first _ ih =>
      have checked := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      have middleHeap := read annotation first semantic (available _ List.mem_cons_self) heap
      exact ih checked.2.1 checked.2.2.1
        (fun child member => checked.1.available child (available child (List.mem_cons_of_mem _ member))) middleHeap

/-- The complete source union retains annotations after its row reads and node request. -/
theorem union (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (trace : SourceEqualityProjectionUnion.Union values before result after) (semantic : SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before) (available : Values before values) (heap : Heap annotation before) : Heap annotation after := by
  cases trace with
  | node rows built =>
      have middleHeap := readAll annotation rows semantic costs available heap
      have final := congrArg Prod.snd built
      dsimp only at final
      rw [← final]
      exact SourceEqualityAnnotationHeap.run annotation _ (SourceEqualityAnnotationHeap.makeNode annotation _) _ middleHeap

private def NodeLaw (annotation : Guard → Prop) (value : Value Symbol Guard) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → InternedFreshOrdinaryCostHeap.Heap before → Available before value → Heap annotation before → Heap annotation after

private def RowsLaw (annotation : Guard → Prop) (edges : List (EdgeValue Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → InternedFreshOrdinaryCostHeap.Heap before → Edges before edges → Heap annotation before → Heap annotation after

private theorem effects (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ path (value : Value Symbol Guard) before result after, Project path value before result after → NodeLaw annotation value before after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsLaw annotation edges before after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeLaw annotation value state state := by
    intro value state _ _ _ heap; exact heap
  have emptyCase : ∀ {state}, NodeLaw annotation (.empty : Value Symbol Guard) state state := by
    intro state _ _ _ heap; exact heap
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      SourceEqualityProjectionUnion.Union values middle result after → RowsLaw annotation edges before middle →
      NodeLaw annotation (.node entry edges depth free) before after := by
    intro path index edges before values middle result after entry depth free trace joined ih semantic costs available heap
    have facts := semantic.ready.semantic.1.normal.facts
    have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
    have rows := SourceEqualityProjectionCosts.rows_effects trace semantic costs resident
    exact union annotation joined rows.2.1 rows.2.2.1 rows.2.2.2 (ih semantic costs resident heap)
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeLaw annotation exposed middle after → NodeLaw annotation original before after := by
    intro original before exposed middle path index result after _ head _ ih semantic costs available heap
    have first := SourceCurrentRequiredHeapEffects.head annotation head semantic costs heap available
    exact ih first.2.1 first.2.2.1 first.2.2.2.2 first.2.2.2.1
  have nilCase : ∀ {state}, RowsLaw annotation ([] : List (EdgeValue Symbol Guard)) state state := by
    intro state _ _ _ heap; exact heap
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsLaw annotation edges before after → RowsLaw annotation (edge :: edges) before after := by
    intro edge path index edges before results after _ _ ih semantic costs resident heap
    exact ih semantic costs (fun value member => resident value (List.mem_cons_of_mem _ member)) heap
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeLaw annotation child before middle →
      RowsLaw annotation edges middle after → RowsLaw annotation (edge :: edges) before after := by
    intro edge index child path before result middle edges results after found firstTrace _ firstIH restIH semantic costs resident heap
    have member := select_member found
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self) child member
    have first := SourceEqualityProjectionCosts.project_effects firstTrace semantic costs available
    have middleHeap := firstIH semantic costs available heap
    exact restIH first.2.1 first.2.2.1
      (fun edge present => InternedEdgeResidency.edge_grows before middle first.1.growth edge (resident edge (List.mem_cons_of_mem _ present)))
      middleHeap
  constructor
  · intro path value before result after trace
    exact Project.rec (motive_1 := fun _ value before _ after _ => NodeLaw annotation value before after)
      (motive_2 := fun _ _ edges before _ after _ => RowsLaw annotation edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace
  · intro path index edges before results after trace
    exact ProjectRows.rec (motive_1 := fun _ value before _ after _ => NodeLaw annotation value before after)
      (motive_2 := fun _ _ edges before _ after _ => RowsLaw annotation edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace

/-- Every completed general node projection preserves physical edge annotations. -/
theorem node (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project path value before result after) (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before) (available : Available before value)
    (heap : Heap annotation before) : Heap annotation after :=
  (effects annotation).1 _ _ _ _ _ trace semantic costs available heap

/-- Every completed ordered row projection preserves the same physical annotation heap. -/
theorem rows (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)} {results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : ProjectRows path index edges before results after) (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before) (resident : Edges before edges)
    (heap : Heap annotation before) : Heap annotation after :=
  (effects annotation).2 _ _ _ _ _ _ trace semantic costs resident heap

/-- Forest projection retains annotations in its root, missing, and selected branches. -/
theorem forest (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Forest path values before result after) (semantic : SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before) (available : Values before values) (heap : Heap annotation before) : Heap annotation after := by
  cases trace with
  | root joined => exact union annotation joined semantic costs available heap
  | missing => exact heap
  | selected found body => exact node annotation body semantic costs (available _ (select_member found)) heap

end MicroCFTA.SourceCurrentOpenProjectionFields
