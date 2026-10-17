import MicroCFTA.SourceCurrentConstrainedCapPathExposure
import MicroCFTA.SourceCurrentConstrainedCapProjection

/-!
# Hereditary endpoints from initial signed path masks

The mask describes the original operands. Actual row, head, and source-union
returns derive hereditary endpoints and retain the causal Mu store. No
uniform path-length condition is required. The finite endpoint theorem
constructs its own projection before it applies the preservation result.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapSupportedProjection
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open SourceEqualityAnnotationLanguage SourceCurrentConstrainedCapPaths
open SourceCurrentHereditaryConstruction (MuStored)
variable {Symbol Guard : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]

private def NodePost (valid : Guard → Prop) (path : List Int) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  SemanticReady before → Available before value → value.free = [] → MuStored valid before → Supported valid path value →
    MuStored valid after ∧ Annotated valid result

private def RowsPost (valid : Guard → Prop) (index : Int) (path : List Int) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (Value Symbol Guard)) (after : State Symbol Guard) : Prop :=
  SemanticReady before → Edges before edges → ClosedEdges edges → MuStored valid before →
    (∀ edge ∈ edges, ∀ child, select edge.children index = some child → Supported valid path child) →
    MuStored valid after ∧ ∀ result ∈ results, Annotated valid result

private theorem all_project (valid : Guard → Prop) :
    (∀ path (value : Value Symbol Guard) before result after, Project path value before result after → NodePost valid path value before result after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsPost valid index path edges before results after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodePost valid [] value state value state := by
    intro value state _ _ _ stored supported
    exact ⟨stored, supported.root⟩
  have emptyCase : ∀ {index path state}, NodePost valid (index :: path) (.empty : Value Symbol Guard) state .empty state := by
    intro index path state _ _ _ stored _
    exact ⟨stored, .empty⟩
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      SourceEqualityProjectionUnion.Union values middle result after → RowsPost valid index path edges before values middle →
      NodePost valid (index :: path) (.node entry edges depth free) before result after := by
    intro path index edges before values middle result after entry depth free rows combined ih semantic available closed stored supported
    have facts := semantic.ready.semantic.1.normal.facts
    have resident := resident_edges before facts.linked _ available.resident
    have rowClosed := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
    have localRows := ih semantic resident rowClosed stored (fun edge member child found => supported.node_selected edge member child found)
    have physical := SourceEqualityProjectionEffects.rows rows semantic resident rowClosed
    have output := SourceCurrentConstrainedCapProjection.union valid 0 combined physical.2.1 physical.2.2.1 physical.2.2.2 localRows.1
      (fun value member => .plain 0 (localRows.2 value member))
    exact ⟨output.1, output.2.annotated rfl⟩
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodePost valid (index :: path) exposed middle result after → NodePost valid (index :: path) original before result after := by
    intro original before exposed middle path index result after _ head _ ih semantic available closed stored supported
    have localHead := SourceCurrentConstrainedCapPathExposure.head valid index path head semantic.ready available closed supported stored
    have physical := head.verified semantic.ready available closed
    exact ih (SourceEqualityRequiredSemanticCache.head head semantic available closed) physical.2.1 physical.2.2.1 localHead.1 localHead.2
  have nilCase : ∀ {index path state}, RowsPost valid index path ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intro index path state _ _ _ stored _
    exact ⟨stored, by intro value member; cases member⟩
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsPost valid index path edges before results after → RowsPost valid index path (edge :: edges) before results after := by
    intro edge path index edges before results after _ _ ih semantic resident closed stored supported
    exact ih semantic (fun edge member => resident edge (List.mem_cons_of_mem _ member))
      (fun edge member => closed edge (List.mem_cons_of_mem _ member)) stored
      (fun edge member => supported edge (List.mem_cons_of_mem _ member))
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodePost valid path child before result middle →
      RowsPost valid index path edges middle results after → RowsPost valid index path (edge :: edges) before (result :: results) after := by
    intro edge index child path before result middle edges results after found first rest firstIH restIH semantic resident closed stored supported
    have member := select_member found
    have childAvailable := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self) child member
    have childClosed := closed edge List.mem_cons_self child member
    have localChild := firstIH semantic childAvailable childClosed stored (supported edge List.mem_cons_self child found)
    have physical := SourceEqualityProjectionEffects.node first semantic childAvailable childClosed
    have tail := restIH physical.2.1
      (fun edge member => edge_grows before middle physical.1.growth edge (resident edge (List.mem_cons_of_mem _ member)))
      (fun edge member => closed edge (List.mem_cons_of_mem _ member)) localChild.1
      (fun edge member => supported edge (List.mem_cons_of_mem _ member))
    refine ⟨tail.1, ?_⟩
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · exact localChild.2
    · exact tail.2 value later
  constructor
  · intro path value before result after actual
    exact Project.rec (motive_1 := fun path value before result after _ => NodePost valid path value before result after)
      (motive_2 := fun path index edges before results after _ => RowsPost valid index path edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual
  · intro path index edges before results after actual
    exact ProjectRows.rec (motive_1 := fun path value before result after _ => NodePost valid path value before result after)
      (motive_2 := fun path index edges before results after _ => RowsPost valid index path edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual

/-- The initial positional mask derives the hereditary result at the exact actual return. -/
theorem node (valid : Guard → Prop)
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project path value before result after) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (stored : MuStored valid before) (supported : Supported valid path value) :
    MuStored valid after ∧ Annotated valid result :=
  (all_project valid).1 _ _ _ _ _ actual semantic available closed stored supported

/-- The distinct forest-root and selected-child branches use their own original masks. -/
theorem forest (valid : Guard → Prop)
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Forest path values before result after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before) (supported : ForestSupported valid path values) :
    MuStored valid after ∧ Annotated valid result := by
  cases actual with
  | root combined =>
      have output := SourceCurrentConstrainedCapProjection.union valid 0 combined semantic available closed stored
        (fun value member => .plain 0 (supported value member))
      exact ⟨output.1, output.2.annotated rfl⟩
  | missing => exact ⟨stored, .empty⟩
  | selected found body => exact node valid body semantic (available _ (select_member found)) (closed _ (select_member found)) stored (supported.selected found)

/-- Initial local support constructs its own finite hereditary projection. -/
theorem complete (valid : Guard → Prop) (path : List Int) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Available before value)
    (closed : value.free = []) (stored : MuStored valid before) (supported : Supported valid path value) :
    ∃ result after, Project path value before result after ∧ Keeps before after ∧ SemanticReady after ∧
      Available after result ∧ result.free = [] ∧ MuStored valid after ∧ Annotated valid result := by
  obtain ⟨result, after, actual, kept, ready, output, outputClosed⟩ :=
    SourceEqualityProjectionComplete.complete path value before semantic available closed
  have localResult := node valid actual semantic available closed stored supported
  exact ⟨result, after, actual, kept, ready, output, outputClosed, localResult⟩

/-- Captured original forest support constructs its own finite hereditary endpoint. -/
theorem forest_complete (valid : Guard → Prop) (path : List Int) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Values before values)
    (closed : ClosedValues values) (stored : MuStored valid before) (supported : ForestSupported valid path values) :
    ∃ result after, Forest path values before result after ∧ Keeps before after ∧ SemanticReady after ∧
      Available after result ∧ result.free = [] ∧ MuStored valid after ∧ Annotated valid result := by
  obtain ⟨result, after, actual, kept, ready, output, outputClosed⟩ :=
    SourceEqualityProjectionComplete.forest_complete path values before semantic available closed
  have localResult := forest valid actual semantic available closed stored supported
  exact ⟨result, after, actual, kept, ready, output, outputClosed, localResult⟩

end MicroCFTA.SourceCurrentConstrainedCapSupportedProjection
