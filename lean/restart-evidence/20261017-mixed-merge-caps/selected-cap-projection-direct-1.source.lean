import MicroCFTA.SourceCurrentConstrainedCapProjection
import MicroCFTA.SourceEqualityProjectionPathComplete

/-!
# Constraint depth through actual selected closed paths

Only selected ordinary children need closed endpoints. Other ordinary
siblings may remain open. Recursive heads keep the existing whole-value
closedness boundary. Each proper child step consumes one finite cap layer.
The first forest index selects a root without consuming that root layer.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapSelectedProjection
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionUnion
open SourceEqualityAnnotationLanguage
open SourceEqualityProjectionPathDomain (NodeClosed RowsClosed ForestClosed)
open SourceCurrentConstrainedCap (Cap Edge)
open SourceCurrentHereditaryConstruction (MuStored)
variable {Symbol Guard : Type}

private theorem edge_child {valid : Guard → Prop} {depth : Nat} {edge : EdgeValue Symbol Guard}
    (bounded : Edge valid depth edge) (child : Value Symbol Guard) (member : child ∈ edge.children) : Cap valid (depth - 1) child := by
  cases depth with
  | zero => exact .plain 0 (bounded.2 child member)
  | succ depth => exact bounded child member

variable [DecidableEq (EdgeKey Symbol Guard)]

private def NodePost (valid : Guard → Prop) (path : List Int) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  ∀ depth, SemanticReady before → Available before value → NodeClosed path value → MuStored valid before → Cap valid depth value →
    MuStored valid after ∧ Cap valid (depth - path.length) result

private def RowsPost (valid : Guard → Prop) (path : List Int) (index : Int) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (Value Symbol Guard)) (after : State Symbol Guard) : Prop :=
  ∀ depth, SemanticReady before → Edges before edges → RowsClosed path index edges → MuStored valid before →
    (∀ edge ∈ edges, Edge valid depth edge) → MuStored valid after ∧ ∀ value ∈ results, Cap valid ((depth - 1) - path.length) value

private theorem all_project (valid : Guard → Prop) :
    (∀ path (value : Value Symbol Guard) before result after, Project path value before result after → NodePost valid path value before result after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsPost valid path index edges before results after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodePost valid [] value state value state := by
    intro value state depth _ _ _ stored bounded
    exact ⟨stored, bounded⟩
  have emptyCase : ∀ {index path state}, NodePost valid (index :: path) (.empty : Value Symbol Guard) state .empty state := by
    intro index path state depth _ _ _ stored _
    exact ⟨stored, .plain _ .empty⟩
  have ordinaryCase : ∀ {path index edges before values middle result after entry level free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle → Union values middle result after →
      RowsPost valid path index edges before values middle → NodePost valid (index :: path) (.node entry edges level free) before result after := by
    intro path index edges before values middle result after entry level free rows combined ih depth semantic available closed stored bounded
    have facts := semantic.ready.semantic.1.normal.facts
    have resident := resident_edges before facts.linked _ available.resident
    have selected : RowsClosed path index edges := by simpa only [NodeClosed, RowsClosed] using closed
    have localRows := ih depth semantic resident selected stored (fun edge member => SourceCurrentConstrainedCap.node_edge bounded edge member)
    have physical := SourceEqualityProjectionPathDomain.rows_effects rows semantic resident selected
    have output := SourceCurrentConstrainedCapProjection.union valid ((depth - 1) - path.length) combined physical.2.1 physical.2.2.1 physical.2.2.2 localRows.1 localRows.2
    have count : (depth - 1) - path.length = depth - (index :: path).length := by simp only [List.length_cons]; omega
    exact ⟨output.1, count ▸ output.2⟩
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodePost valid (index :: path) exposed middle result after → NodePost valid (index :: path) original before result after := by
    intro original before exposed middle path index result after recursive head next _ depth semantic available domain stored bounded
    exact SourceCurrentConstrainedCapProjection.node valid depth (.recursive recursive head next) semantic available
      (SourceEqualityProjectionPathDomain.recursive_closed recursive domain) stored bounded
  have nilCase : ∀ {path index state}, RowsPost valid path index ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intro path index state depth _ _ _ stored _
    exact ⟨stored, by intro value member; cases member⟩
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsPost valid path index edges before results after → RowsPost valid path index (edge :: edges) before results after := by
    intro edge path index edges before results after _ _ ih depth semantic resident closed stored bounded
    exact ih depth semantic (fun edge member => resident edge (List.mem_cons_of_mem _ member))
      (fun edge member => closed edge (List.mem_cons_of_mem _ member)) stored
      (fun edge member => bounded edge (List.mem_cons_of_mem _ member))
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodePost valid path child before result middle →
      RowsPost valid path index edges middle results after → RowsPost valid path index (edge :: edges) before (result :: results) after := by
    intro edge index child path before result middle edges results after found first rest firstIH restIH depth semantic resident closed stored bounded
    have member := select_member found
    have childAvailable := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self) child member
    have childDomain := closed edge List.mem_cons_self child found
    have localChild := firstIH (depth - 1) semantic childAvailable childDomain stored (edge_child (bounded edge List.mem_cons_self) child member)
    have physical := SourceEqualityProjectionPathDomain.node_effects first semantic childAvailable childDomain
    have tail := restIH depth physical.2.1
      (fun edge member => edge_grows before middle physical.1.growth edge (resident edge (List.mem_cons_of_mem _ member)))
      (fun edge member => closed edge (List.mem_cons_of_mem _ member)) localChild.1
      (fun edge member => bounded edge (List.mem_cons_of_mem _ member))
    refine ⟨tail.1, ?_⟩
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · exact localChild.2
    · exact tail.2 value later
  constructor
  · intro path value before result after actual
    exact Project.rec (motive_1 := fun path value before result after _ => NodePost valid path value before result after)
      (motive_2 := fun path index edges before results after _ => RowsPost valid path index edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual
  · intro path index edges before results after actual
    exact ProjectRows.rec (motive_1 := fun path value before result after _ => NodePost valid path value before result after)
      (motive_2 := fun path index edges before results after _ => RowsPost valid path index edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual

/-- Selected ordinary child steps consume a layer without closing unrelated siblings. -/
theorem node (valid : Guard → Prop) (depth : Nat)
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project path value before result after) (semantic : SemanticReady before)
    (available : Available before value) (closed : NodeClosed path value) (stored : MuStored valid before) (bounded : Cap valid depth value) :
    MuStored valid after ∧ Cap valid (depth - path.length) result :=
  (all_project valid).1 _ _ _ _ _ actual depth semantic available closed stored bounded

/-- Every selected row output retains its shorter finite bound at the same returned heap. -/
theorem rows (valid : Guard → Prop) (depth : Nat)
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)}
    {results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : ProjectRows path index edges before results after) (semantic : SemanticReady before)
    (resident : Edges before edges) (domain : RowsClosed path index edges) (stored : MuStored valid before)
    (bounded : ∀ edge ∈ edges, Edge valid depth edge) :
    MuStored valid after ∧ ∀ value ∈ results, Cap valid ((depth - 1) - path.length) value :=
  (all_project valid).2 _ _ _ _ _ _ actual depth semantic resident domain stored bounded

/-- The first forest index selects an original root; only that selected route needs closure. -/
theorem forest (valid : Guard → Prop) (depth : Nat)
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Forest path values before result after) (semantic : SemanticReady before)
    (available : Values before values) (domain : ForestClosed path values) (stored : MuStored valid before)
    (bounded : ∀ value ∈ values, Cap valid depth value) :
    MuStored valid after ∧ Cap valid (depth - (path.length - 1)) result := by
  cases actual with
  | root combined => exact SourceCurrentConstrainedCapProjection.union valid depth combined semantic available domain stored bounded
  | missing => exact ⟨stored, .plain _ .empty⟩
  | selected found body =>
      exact node valid depth body semantic (available _ (select_member found)) (domain _ found) stored (bounded _ (select_member found))

/-- Initial selected-domain facts construct their own finite node projection and output cap. -/
theorem complete (valid : Guard → Prop) (depth : Nat) (path : List Int) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Available before value)
    (domain : NodeClosed path value) (stored : MuStored valid before) (bounded : Cap valid depth value) :
    ∃ result after, Project path value before result after ∧ Keeps before after ∧ SemanticReady after ∧
      Available after result ∧ result.free = [] ∧ MuStored valid after ∧ Cap valid (depth - path.length) result := by
  obtain ⟨result, after, actual, kept, ready, output, closed⟩ :=
    SourceEqualityProjectionPathComplete.node_complete path value before semantic available domain
  exact ⟨result, after, actual, kept, ready, output, closed,
    node valid depth actual semantic available domain stored bounded⟩

/-- Initial forest masks construct a finite projection without a closedness premise for every root. -/
theorem forest_complete (valid : Guard → Prop) (depth : Nat) (path : List Int) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Values before values)
    (domain : ForestClosed path values) (stored : MuStored valid before) (bounded : ∀ value ∈ values, Cap valid depth value) :
    ∃ result after, Forest path values before result after ∧ Keeps before after ∧ SemanticReady after ∧
      Available after result ∧ result.free = [] ∧ MuStored valid after ∧ Cap valid (depth - (path.length - 1)) result := by
  obtain ⟨result, after, actual, kept, ready, output, closed⟩ :=
    SourceEqualityProjectionPathComplete.forest_complete path values before semantic available domain
  exact ⟨result, after, actual, kept, ready, output, closed,
    forest valid depth actual semantic available domain stored bounded⟩

end MicroCFTA.SourceCurrentConstrainedCapSelectedProjection
