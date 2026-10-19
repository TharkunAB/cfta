import MicroCFTA.SourceCurrentConstrainedCapOpenExposure
import MicroCFTA.SourceCurrentConstrainedCapProjectionGuard

/-!
# Hereditary annotations through actual open projection and later reads

Actual projection preserves an annotated input through its selected children,
recursive Heads, and union reads. The terminal read uses its own semantic,
availability, and guard-heap support. No input closedness or changed-input
gate is required. These laws classify completed calls, not future completion.
-/
namespace MicroCFTA.SourceCurrentRecursivePlainRead
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap (Cap Edge)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap

private theorem read_rows (annotation : Guard → Prop) {value : Node} {before rows after}
    (actual : Read value before rows after) (semantic : SemanticReady before)
    (available : Available before value) (guards : Guards annotation before)
    (annotated : Annotated annotation value) : ∀ row ∈ rows, Edge annotation 0 row := by
  cases actual with
  | done fuel completed =>
    exact (SourceCurrentConstrainedCapOpenExposure.nodeEdges annotation 0 fuel value before
      semantic.ready.semantic semantic.ready.covered available (.plain 0 annotated)
      (SourceCurrentConstrainedCapGuardNative.stored annotation before guards) rows after completed).2

private theorem union_annotated (annotation : Guard → Prop) {values before result after}
    (actual : Union (Symbol := Symbol) (Guard := Guard) values before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (guards : Guards annotation before) (annotated : ∀ value ∈ values, Annotated annotation value) :
    Annotated annotation result := by
  have rowsAnnotated : ∀ {values before rows after}, ReadAll values before rows after →
      SemanticReady before → CostHeap before → Values before values → Guards annotation before →
      (∀ value ∈ values, Annotated annotation value) → ∀ row ∈ rows, Edge annotation 0 row := by
    intro values before rows after reads
    induction reads with
    | nil => intro _ _ _ _ _ row member; cases member
    | @cons value before own middle values more after first rest ih =>
      intro semantic costs available guards annotated row member
      have physical := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      rcases List.mem_append.mp member with here | later
      · exact read_rows annotation first semantic (available _ List.mem_cons_self) guards
          (annotated _ List.mem_cons_self) row here
      · exact ih physical.2.1 physical.2.2.1
          (fun value member => physical.1.available value (available value (List.mem_cons_of_mem _ member)))
          (SourceCurrentConstrainedCapProjectionGuard.read annotation first semantic costs (available _ List.mem_cons_self) guards)
          (fun value member => annotated value (List.mem_cons_of_mem _ member)) row later
  cases actual with
  | node reads built =>
    have effects := SourceEqualityProjectionCosts.readAll_effects reads semantic costs available
    have bounded := SourceCurrentConstrainedCap.makeNode annotation 0 _ _
      effects.2.1.ready.semantic.1.normal.facts.coherent effects.2.1.ready.semantic.1.normal.facts.linked
      effects.2.2.2 (rowsAnnotated reads semantic costs available guards annotated)
    simpa only [built] using bounded.annotated rfl

private def NodeLaw (annotation : Guard → Prop) (value : Node) (before : Heap) (result : Node) : Prop :=
  SemanticReady before → CostHeap before → Available before value → Guards annotation before →
    Annotated annotation value → Annotated annotation result

private def RowsLaw (annotation : Guard → Prop) (rows : List Row) (before : Heap) (values : List Node) : Prop :=
  SemanticReady before → CostHeap before → Edges before rows → Guards annotation before →
    (∀ row ∈ rows, ∀ child ∈ row.children, Annotated annotation child) →
    ∀ value ∈ values, Annotated annotation value

private theorem projection (annotation : Guard → Prop) :
    (∀ path value before result after, Project path value before result after → NodeLaw annotation value before result) ∧
    (∀ path index rows before values after, ProjectRows path index rows before values after → RowsLaw annotation rows before values) := by
  have rootCase : ∀ {value state}, NodeLaw annotation value state value := by
    intro value state _ _ _ _ annotated; exact annotated
  have emptyCase : ∀ {state}, NodeLaw annotation (.empty : Node) state .empty := by
    intro state _ _ _ _ _; exact .empty
  have ordinaryCase : ∀ {path index rows before values middle result after entry depth free},
      ProjectRows path index rows before values middle → Union values middle result after →
      RowsLaw annotation rows before values → NodeLaw annotation (.node entry rows depth free) before result := by
    intro path index rows before values middle result after entry depth free actual joined ih semantic costs available guards annotated
    have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have physical := SourceEqualityProjectionCosts.rows_effects actual semantic costs resident
    have children : ∀ row ∈ rows, ∀ child ∈ row.children, Annotated annotation child := by
      cases annotated with
      | node _ _ _ _ _ children =>
        exact fun row member child inside => children child (List.mem_flatMap.mpr ⟨row,member,inside⟩)
    have valuesAnnotated := ih semantic costs resident guards children
    have nextGuards := SourceCurrentConstrainedCapProjectionGuard.node annotation
      (.ordinary (entry := entry) (depth := depth) (free := free) actual joined) semantic costs available guards
    have middleGuards : Guards annotation middle := by
      -- The ordinary union follows this actual row scan. Its earlier heap is restricted from its final heap.
      have unionGrowth := SourceEqualityProjectionCosts.union_effects joined physical.2.1 physical.2.2.1 physical.2.2.2
      intro key entry body depth ordinary present
      exact nextGuards key entry body depth ordinary (unionGrowth.1.growth.nodeRecords key _ present)
    exact union_annotated annotation joined physical.2.1 physical.2.2.1 physical.2.2.2 middleGuards valuesAnnotated
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (index :: path) exposed middle result after → NodeLaw annotation exposed middle result →
      NodeLaw annotation original before result := by
    intro original before exposed middle path index result after _ head _ ih semantic costs available guards annotated
    have bounded := SourceCurrentConstrainedCapOpenExposure.head annotation 0 head semantic costs available
      (.plain 0 annotated) (SourceCurrentConstrainedCapGuardNative.stored annotation before guards)
    have physical := SourceEqualityProjectionCosts.head_effects head semantic costs available
    exact ih physical.2.1 physical.2.2.1 physical.2.2.2
      (SourceCurrentConstrainedCapProjectionGuard.head annotation head semantic costs available guards)
      (bounded.2.annotated rfl)
  have nilCase : ∀ {state}, RowsLaw annotation [] state [] := by
    intro state _ _ _ _ _ value member; cases member
  have missingCase : ∀ {row path index rows before values after}, select row.children index = none →
      ProjectRows path index rows before values after → RowsLaw annotation rows before values →
      RowsLaw annotation (row :: rows) before values := by
    intro row path index rows before values after _ _ ih semantic costs resident guards annotated
    exact ih semantic costs (fun row member => resident row (List.mem_cons_of_mem _ member)) guards
      (fun row member => annotated row (List.mem_cons_of_mem _ member))
  have selectedCase : ∀ {row index child path before result middle rows values after},
      select row.children index = some child → Project path child before result middle →
      ProjectRows path index rows middle values after → NodeLaw annotation child before result →
      RowsLaw annotation rows middle values → RowsLaw annotation (row :: rows) before (result :: values) := by
    intro row index child path before result middle rows values after found actual rest firstIH restIH
      semantic costs resident guards annotated
    have available := semantic.ready.semantic.1.normal.facts.cached.edges row.entry.key row
      (resident row List.mem_cons_self) child (select_member found)
    have physical := SourceEqualityProjectionCosts.project_effects actual semantic costs available
    have first := firstIH semantic costs available guards (annotated row List.mem_cons_self child (select_member found))
    have later := restIH physical.2.1 physical.2.2.1
      (fun row member => edge_grows before middle physical.1.growth row (resident row (List.mem_cons_of_mem _ member)))
      (SourceCurrentConstrainedCapProjectionGuard.node annotation actual semantic costs available guards)
      (fun row member => annotated row (List.mem_cons_of_mem _ member))
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact later value member
  constructor
  · intro path value before result after actual
    exact Project.rec (motive_1 := fun _ value before result _ _ => NodeLaw annotation value before result)
      (motive_2 := fun _ _ rows before values _ _ => RowsLaw annotation rows before values)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual
  · intro path index rows before values after actual
    exact ProjectRows.rec (motive_1 := fun _ value before result _ _ => NodeLaw annotation value before result)
      (motive_2 := fun _ _ rows before values _ _ => RowsLaw annotation rows before values)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual

/-- Actual signed projection preserves hereditary annotations without a closedness premise. -/
theorem project (annotation : Guard → Prop) {path value before result after}
    (actual : Project (Symbol := Symbol) (Guard := Guard) path value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (guards : Guards annotation before) (annotated : Annotated annotation value) : Annotated annotation result :=
  projection annotation |>.1 _ _ _ _ _ actual semantic costs available guards annotated

/-- A later actual row read of an annotated projection satisfies the same guard predicate. -/
theorem project_read (annotation : Guard → Prop) {path value before result after}
    (actual : Project (Symbol := Symbol) (Guard := Guard) path value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (guards : Guards annotation before) (annotated : Annotated annotation value)
    {reader rows readAfter} (read : Read result reader rows readAfter)
    (readerSemantic : SemanticReady reader) (later : Keeps after reader) (readerGuards : Guards annotation reader)
    (row : Row) (selected : row ∈ rows) : annotation row.entry.key.constraint := by
  have resultAnnotated := project annotation actual semantic costs available guards annotated
  have effects := SourceEqualityProjectionCosts.project_effects actual semantic costs available
  exact (read_rows annotation read readerSemantic (later.available result effects.2.2.2) readerGuards resultAnnotated row selected).1

end MicroCFTA.SourceCurrentRecursivePlainRead
