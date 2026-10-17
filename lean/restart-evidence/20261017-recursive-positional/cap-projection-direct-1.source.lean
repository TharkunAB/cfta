import MicroCFTA.SourceCurrentConstrainedCapExposure
import MicroCFTA.SourceEqualityNativeProjection

/-!
# Constraint depth through actual signed path projection

Each ordinary child step consumes one finite constraint layer. Actual Mu
and union heads retain the remaining bound. Closed source unions combine
the returned rows at that same bound. These are preservation results for
completed projection graphs. They do not prove general selected execution.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapProjection
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionUnion
open SourceEqualityAnnotationLanguage SourceCurrentConstrainedCap (Cap Edge)
open SourceCurrentHereditaryConstruction (MuStored)
variable {Symbol Guard : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- One exact completed row read retains the finite bound and causal store. -/
theorem read (valid : Guard → Prop) (depth : Nat)
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : SourceEqualityProjectionRead.Read value before edges after) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (stored : MuStored valid before) (bounded : Cap valid depth value) :
    MuStored valid after ∧ ∀ edge ∈ edges, Edge valid depth edge := by
  cases actual with
  | done fuel done =>
      exact SourceCurrentConstrainedCapExposure.nodeEdges valid depth fuel value before semantic.ready.semantic semantic.ready.covered
        available closed bounded stored edges after done

/-- Ordered original operands retain their bound at each actual returned row heap. -/
theorem readAll (valid : Guard → Prop) (depth : Nat)
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : ReadAll values before edges after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (bounded : ∀ value ∈ values, Cap valid depth value) : MuStored valid after ∧ ∀ edge ∈ edges, Edge valid depth edge := by
  induction actual with
  | nil => exact ⟨stored, by intro edge member; cases member⟩
  | @cons value before rows middle values more after first rest ih =>
      have firstLocal := read valid depth first semantic (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
        stored (bounded _ List.mem_cons_self)
      have firstEffects := first.verified semantic (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
      have tail := ih firstEffects.2.1
        (fun value member => firstEffects.1.available value (available value (List.mem_cons_of_mem _ member)))
        (fun value member => closed value (List.mem_cons_of_mem _ member)) firstLocal.1
        (fun value member => bounded value (List.mem_cons_of_mem _ member))
      refine ⟨tail.1, ?_⟩
      intro edge member
      rcases List.mem_append.mp member with original | later
      · exact firstLocal.2 edge original
      · exact tail.2 edge later

/-- Actual closed source union retains its supplied finite constraint bound. -/
theorem union (valid : Guard → Prop) (depth : Nat)
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (actual : Union values before result after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (bounded : ∀ value ∈ values, Cap valid depth value) : MuStored valid after ∧ Cap valid depth result := by
  cases actual with
  | node rows built =>
      have localRows := readAll valid depth rows semantic available closed stored bounded
      have effects := rows.verified semantic available closed
      have facts := effects.2.1.ready.semantic.1.normal.facts
      exact ⟨by simpa only [built] using localRows.1.makeNode _,
        by simpa only [built] using SourceCurrentConstrainedCap.makeNode valid depth _ _ facts.coherent facts.linked effects.2.2.1 localRows.2⟩

private def NodePost (valid : Guard → Prop) (path : List Int) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  ∀ depth, SemanticReady before → Available before value → value.free = [] → MuStored valid before → Cap valid depth value →
    MuStored valid after ∧ Cap valid (depth - path.length) result

private def RowsPost (valid : Guard → Prop) (path : List Int) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (Value Symbol Guard)) (after : State Symbol Guard) : Prop :=
  ∀ depth, SemanticReady before → Edges before edges → ClosedEdges edges → MuStored valid before →
    (∀ edge ∈ edges, Edge valid depth edge) → MuStored valid after ∧ ∀ value ∈ results, Cap valid ((depth - 1) - path.length) value

private theorem edge_child {valid : Guard → Prop} {depth : Nat} {edge : EdgeValue Symbol Guard}
    (bounded : Edge valid depth edge) (child : Value Symbol Guard) (member : child ∈ edge.children) : Cap valid (depth - 1) child := by
  cases depth with
  | zero => exact .plain 0 (bounded.2 child member)
  | succ depth => exact bounded child member

private theorem all_project (valid : Guard → Prop) :
    (∀ path (value : Value Symbol Guard) before result after, Project path value before result after → NodePost valid path value before result after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsPost valid path edges before results after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodePost valid [] value state value state := by
    intro value state depth _ _ _ stored bounded
    exact ⟨stored, bounded⟩
  have emptyCase : ∀ {index path state}, NodePost valid (index :: path) (.empty : Value Symbol Guard) state .empty state := by
    intro index path state depth _ _ _ stored _
    exact ⟨stored, .plain _ .empty⟩
  have ordinaryCase : ∀ {path index edges before values middle result after entry level free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle → Union values middle result after →
      RowsPost valid path edges before values middle → NodePost valid (index :: path) (.node entry edges level free) before result after := by
    intro path index edges before values middle result after entry level free rows combined ih depth semantic available closed stored bounded
    have facts := semantic.ready.semantic.1.normal.facts
    have resident := resident_edges before facts.linked _ available.resident
    have rowClosed := MergedColdReaderClosed.node_children_closed before facts entry edges level free available closed
    have localRows := ih depth semantic resident rowClosed stored (fun edge member => SourceCurrentConstrainedCap.node_edge bounded edge member)
    have physical := SourceEqualityProjectionEffects.rows rows semantic resident rowClosed
    have output := union valid ((depth - 1) - path.length) combined physical.2.1 physical.2.2.1 physical.2.2.2 localRows.1 localRows.2
    have count : (depth - 1) - path.length = depth - (index :: path).length := by simp only [List.length_cons]; omega
    exact ⟨output.1, count ▸ output.2⟩
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodePost valid (index :: path) exposed middle result after → NodePost valid (index :: path) original before result after := by
    intro original before exposed middle path index result after _ head _ ih depth semantic available closed stored bounded
    have localHead := SourceCurrentConstrainedCapExposure.head valid depth head semantic.ready available closed bounded stored
    have physical := head.verified semantic.ready available closed
    exact ih depth (SourceEqualityRequiredSemanticCache.head head semantic available closed) physical.2.1 physical.2.2.1 localHead.1 localHead.2
  have nilCase : ∀ {path state}, RowsPost valid path ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intro path state depth _ _ _ stored _
    exact ⟨stored, by intro value member; cases member⟩
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsPost valid path edges before results after → RowsPost valid path (edge :: edges) before results after := by
    intro edge path index edges before results after _ _ ih depth semantic resident closed stored bounded
    exact ih depth semantic (fun edge member => resident edge (List.mem_cons_of_mem _ member))
      (fun edge member => closed edge (List.mem_cons_of_mem _ member)) stored
      (fun edge member => bounded edge (List.mem_cons_of_mem _ member))
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodePost valid path child before result middle →
      RowsPost valid path edges middle results after → RowsPost valid path (edge :: edges) before (result :: results) after := by
    intro edge index child path before result middle edges results after found first rest firstIH restIH depth semantic resident closed stored bounded
    have member := select_member found
    have childAvailable := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self) child member
    have childClosed := closed edge List.mem_cons_self child member
    have localChild := firstIH (depth - 1) semantic childAvailable childClosed stored (edge_child (bounded edge List.mem_cons_self) child member)
    have physical := SourceEqualityProjectionEffects.node first semantic childAvailable childClosed
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
      (motive_2 := fun path _ edges before results after _ => RowsPost valid path edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual
  · intro path index edges before results after actual
    exact ProjectRows.rec (motive_1 := fun path value before result after _ => NodePost valid path value before result after)
      (motive_2 := fun path _ edges before results after _ => RowsPost valid path edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual

/-- Every actual ordinary child step consumes one remaining constrained layer. -/
theorem node (valid : Guard → Prop) (depth : Nat)
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project path value before result after) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (stored : MuStored valid before) (bounded : Cap valid depth value) :
    MuStored valid after ∧ Cap valid (depth - path.length) result :=
  (all_project valid).1 _ _ _ _ _ actual depth semantic available closed stored bounded

/-- A sufficiently long initial path returns a hereditary endpoint at its actual heap. -/
theorem endpoint (valid : Guard → Prop) (depth : Nat)
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project path value before result after) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (stored : MuStored valid before)
    (bounded : Cap valid depth value) (long : depth ≤ path.length) : MuStored valid after ∧ Annotated valid result := by
  have output := node valid depth actual semantic available closed stored bounded
  exact ⟨output.1, output.2.annotated (Nat.sub_eq_zero_of_le long)⟩

/-- The forest's first index selects an original root without consuming its cap depth. -/
theorem forest (valid : Guard → Prop) (depth : Nat)
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Forest path values before result after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (bounded : ∀ value ∈ values, Cap valid depth value) :
    MuStored valid after ∧ Cap valid (depth - (path.length - 1)) result := by
  cases actual with
  | root combined => exact union valid depth combined semantic available closed stored bounded
  | missing => exact ⟨stored, .plain _ .empty⟩
  | selected found body =>
      exact node valid depth body semantic (available _ (select_member found)) (closed _ (select_member found)) stored (bounded _ (select_member found))

end MicroCFTA.SourceCurrentConstrainedCapProjection
