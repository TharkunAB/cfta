import MicroCFTA.SourceCurrentHereditaryExposure
import MicroCFTA.SourceEqualityProjectionEffects

/-!
# Local annotations through actual path projection

Projection follows its actual row, head, and union calls. An ordinary row
needs an annotation only at its selected child position. Other guards and
children in the same forest can remain outside the annotation predicate.
The laws describe completed graphs. They do not establish completion.
-/
namespace MicroCFTA.SourceCurrentHereditaryProjection
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionUnion
open SourceEqualityAnnotationLanguage (Annotated)
open SourceCurrentHereditaryConstruction (MuStored)
variable {Symbol Guard : Type}

/-- Only children at the actual selected row position need annotations. -/
def SelectedFields (valid : Guard → Prop) (index : Int) (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ edge ∈ edges, ∀ child, select edge.children index = some child → Annotated valid child

private theorem readAll [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : ReadAll values before edges after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (annotated : ∀ value ∈ values, Annotated valid value) :
    MuStored valid after ∧ ∀ edge ∈ edges, SourceCurrentHereditaryConstructors.Edge valid edge := by
  induction actual with
  | nil => exact ⟨stored, by intro edge member; cases member⟩
  | @cons value before rows middle values more after first rest ih =>
      have physical := first.verified semantic (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
      have own : MuStored valid middle ∧
          ∀ edge ∈ rows, SourceCurrentHereditaryConstructors.Edge valid edge := by
        cases first with
        | done fuel completed =>
            exact SourceCurrentHereditaryExposure.nodeEdges valid fuel value before
              semantic.ready.semantic semantic.ready.covered (available _ List.mem_cons_self)
              (closed _ List.mem_cons_self) (annotated _ List.mem_cons_self) stored rows middle completed
      have later := ih physical.2.1
        (fun value member => physical.1.available value (available value (List.mem_cons_of_mem _ member)))
        (fun value member => closed value (List.mem_cons_of_mem _ member)) own.1
        (fun value member => annotated value (List.mem_cons_of_mem _ member))
      refine ⟨later.1, ?_⟩
      intro edge member
      rcases List.mem_append.mp member with first | rest
      · exact own.2 edge first
      · exact later.2 edge rest

/-- The actual source union reads only its annotated projected operands. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (actual : Union values before result after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (annotated : ∀ value ∈ values, Annotated valid value) :
    MuStored valid after ∧ Annotated valid result := by
  cases actual with
  | node read built =>
      rename_i edges middle
      have rows := readAll valid read semantic available closed stored annotated
      have physical := read.verified semantic available closed
      have facts := physical.2.1.ready.semantic.1.normal.facts
      constructor
      · simpa only [built] using rows.1.makeNode edges
      · simpa only [built] using SourceCurrentHereditaryConstructors.makeNode valid edges middle
          facts.coherent facts.linked physical.2.2.1 rows.2

private def NodeResult (valid : Guard → Prop) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  SemanticReady before → Available before value → value.free = [] →
    MuStored valid before → Annotated valid value → MuStored valid after ∧ Annotated valid result

private def RowsResult (valid : Guard → Prop) (index : Int) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (Value Symbol Guard)) (after : State Symbol Guard) : Prop :=
  SemanticReady before → Edges before edges → ClosedEdges edges → MuStored valid before →
    SelectedFields valid index edges → MuStored valid after ∧ ∀ value ∈ results, Annotated valid value

private theorem projection [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) :
    (∀ path (value : Value Symbol Guard) before result after,
      Project path value before result after → NodeResult valid value before result after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsResult valid index edges before results after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeResult valid value state value state := by
    intro value state _ _ _ stored annotated
    exact ⟨stored, annotated⟩
  have emptyCase : ∀ {state}, NodeResult valid (.empty : Value Symbol Guard) state .empty state := by
    intro state _ _ _ stored _
    exact ⟨stored, .empty⟩
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      Union values middle result after → RowsResult valid index edges before values middle →
      NodeResult valid (.node entry edges depth free) before result after := by
    intro path index edges before values middle result after entry depth free rows combined ih
      semantic available closed stored annotated
    have facts := semantic.ready.semantic.1.normal.facts
    have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
    have rowClosed := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
    have selected : SelectedFields valid index edges := by
      intro edge member child found
      exact (SourceCurrentHereditaryConstructors.node_edge annotated edge member).2 child (select_member found)
    have localRows := ih semantic resident rowClosed stored selected
    have physical := SourceEqualityProjectionEffects.rows rows semantic resident rowClosed
    exact union valid combined physical.2.1 physical.2.2.1 physical.2.2.2 localRows.1 localRows.2
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeResult valid exposed middle result after → NodeResult valid original before result after := by
    intro original before exposed middle path index result after _ head _ ih semantic available closed stored annotated
    have localHead := SourceCurrentHereditaryExposure.head valid head semantic.ready available closed annotated stored
    have physical := head.verified semantic.ready available closed
    exact ih (SourceEqualityRequiredSemanticCache.head head semantic available closed)
      physical.2.1 physical.2.2.1 localHead.1 localHead.2
  have nilCase : ∀ {index : Int} {state},
      RowsResult valid index ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intro index state _ _ _ stored _
    exact ⟨stored, by intro value member; cases member⟩
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsResult valid index edges before results after → RowsResult valid index (edge :: edges) before results after := by
    intro edge path index edges before results after _ _ ih semantic resident closed stored selected
    exact ih semantic (fun edge member => resident edge (List.mem_cons_of_mem _ member))
      (fun edge member => closed edge (List.mem_cons_of_mem _ member)) stored
      (fun edge member => selected edge (List.mem_cons_of_mem _ member))
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeResult valid child before result middle →
      RowsResult valid index edges middle results after → RowsResult valid index (edge :: edges) before (result :: results) after := by
    intro edge index child path before result middle edges results after found first rest firstIH restIH
      semantic resident closed stored selected
    have facts := semantic.ready.semantic.1.normal.facts
    have member := select_member found
    have available := facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self) child member
    have childClosed := closed edge List.mem_cons_self child member
    have own := firstIH semantic available childClosed stored (selected edge List.mem_cons_self child found)
    have physical := SourceEqualityProjectionEffects.node first semantic available childClosed
    have later := restIH physical.2.1
      (fun edge member => InternedEdgeResidency.edge_grows before middle physical.1.growth edge
        (resident edge (List.mem_cons_of_mem _ member)))
      (fun edge member => closed edge (List.mem_cons_of_mem _ member)) own.1
      (fun edge member => selected edge (List.mem_cons_of_mem _ member))
    refine ⟨later.1, ?_⟩
    intro value present
    rcases List.mem_cons.mp present with rfl | tail
    · exact own.2
    · exact later.2 value tail
  constructor
  · intro path value before result after actual
    exact Project.rec (motive_1 := fun _ value before result after _ => NodeResult valid value before result after)
      (motive_2 := fun _ index edges before results after _ => RowsResult valid index edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual
  · intro path index edges before results after actual
    exact ProjectRows.rec (motive_1 := fun _ value before result after _ => NodeResult valid value before result after)
      (motive_2 := fun _ index edges before results after _ => RowsResult valid index edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual

/-- Every completed projection of an annotated Type retains its local certificate. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project path value before result after) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (stored : MuStored valid before)
    (annotated : Annotated valid value) : MuStored valid after ∧ Annotated valid result :=
  (projection valid).1 _ _ _ _ _ actual semantic available closed stored annotated

/-- Actual row projection needs annotations only on its selected children. -/
theorem rows [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)}
    {results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : ProjectRows path index edges before results after) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (stored : MuStored valid before)
    (selected : SelectedFields valid index edges) :
    MuStored valid after ∧ ∀ value ∈ results, Annotated valid value :=
  (projection valid).2 _ _ _ _ _ _ actual semantic resident closed stored selected

/-- A mixed ordinary Program node can project its Type fields without annotating its guards. -/
theorem ordinary [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {path : List Int} {index : Int} {entry : Interned InternedBinderProtocol.NodeKey}
    {edges : List (EdgeValue Symbol Guard)} {depth : Nat} {free : List InternedBinderProtocol.Reference}
    {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project (index :: path) (.node entry edges depth free) before result after)
    (semantic : SemanticReady before) (available : Available before (.node entry edges depth free))
    (closed : (Value.node entry edges depth free).free = []) (stored : MuStored valid before)
    (selected : SelectedFields valid index edges) : MuStored valid after ∧ Annotated valid result := by
  cases actual with
  | ordinary projected combined =>
      have facts := semantic.ready.semantic.1.normal.facts
      have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
      have rowClosed := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
      have localRows := rows valid projected semantic resident rowClosed stored selected
      have physical := SourceEqualityProjectionEffects.rows projected semantic resident rowClosed
      exact union valid combined physical.2.1 physical.2.2.1 physical.2.2.2 localRows.1 localRows.2
  | recursive recursive _ _ => cases recursive

/-- Forest selection needs an annotation only on the selected original root. -/
theorem forest_selected [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {path : List Int} {index : Int} {values : List (Value Symbol Guard)}
    {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Forest (index :: path) values before result after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (selected : ∀ value, select values index = some value → Annotated valid value) :
    MuStored valid after ∧ Annotated valid result := by
  cases actual with
  | missing => exact ⟨stored, .empty⟩
  | selected found body =>
      exact node valid body semantic (available _ (select_member found))
        (closed _ (select_member found)) stored (selected _ found)

end MicroCFTA.SourceCurrentHereditaryProjection
