import MicroCFTA.SourceCurrentHereditaryProjection

/-!
# Structural routes to Type fields

An input route can pass through ordinary Program nodes before it enters an
annotated Type. Other row guards and siblings need no annotation. The route
contains no projected result or future execution. Unannotated recursive or
stored union Program heads have no route constructor in this certificate.
-/
namespace MicroCFTA.SourceCurrentHereditaryTypePaths
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph
open SourceEqualityAnnotationLanguage (Annotated)
open SourceCurrentHereditaryConstruction (MuStored)
variable {Symbol Guard : Type}

/-- A route reaches an annotated Type through the selected ordinary children. -/
inductive TypePath (valid : Guard → Prop) : List Int → Value Symbol Guard → Prop where
  /-- Once the value is a Type, every actual continuation path is permitted. -/
  | annotated (path : List Int) (value : Value Symbol Guard) (checked : Annotated valid value) :
      TypePath valid path value
  /-- An ordinary Program prefix supplies routes only for children at the selected index. -/
  | ordinary {index : Int} {path : List Int} {entry : Interned InternedBinderProtocol.NodeKey}
      {edges : List (EdgeValue Symbol Guard)} {depth : Nat} {free : List InternedBinderProtocol.Reference}
      (children : ∀ edge ∈ edges, ∀ child,
        select edge.children index = some child → TypePath valid path child) :
      TypePath valid (index :: path) (.node entry edges depth free)

/-- Forest roots use all operands only at the empty path. -/
def ForestPath (valid : Guard → Prop) : List Int → List (Value Symbol Guard) → Prop
  | [], values => ∀ value ∈ values, Annotated valid value
  | index :: path, values => ∀ value, select values index = some value → TypePath valid path value

private def NodeResult [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (path : List Int) (value : Value Symbol Guard) : Prop :=
  ∀ (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard),
    Project path value before result after → SemanticReady before → Available before value → value.free = [] →
      MuStored valid before → MuStored valid after ∧ Annotated valid result

private theorem rows_from_calls [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)}
    {results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : ProjectRows path index edges before results after) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (stored : MuStored valid before)
    (calls : ∀ edge ∈ edges, ∀ child,
      select edge.children index = some child → NodeResult valid path child) :
    MuStored valid after ∧ ∀ value ∈ results, Annotated valid value := by
  cases actual with
  | nil => exact ⟨stored, by intro value member; cases member⟩
  | missing absent rest =>
      exact rows_from_calls valid rest semantic (fun edge member => resident edge (List.mem_cons_of_mem _ member))
        (fun edge member => closed edge (List.mem_cons_of_mem _ member)) stored
        (fun edge member => calls edge (List.mem_cons_of_mem _ member))
  | selected found first rest =>
      have facts := semantic.ready.semantic.1.normal.facts
      have member := select_member found
      have available := facts.cached.edges _ _ (resident _ List.mem_cons_self) _ member
      have childClosed := closed _ List.mem_cons_self _ member
      have own := calls _ List.mem_cons_self _ found _ _ _ first semantic available childClosed stored
      have physical := SourceEqualityProjectionEffects.node first semantic available childClosed
      have later := rows_from_calls valid rest physical.2.1
        (fun edge member => InternedEdgeResidency.edge_grows _ _ physical.1.growth edge
          (resident edge (List.mem_cons_of_mem _ member)))
        (fun edge member => closed edge (List.mem_cons_of_mem _ member)) own.1
        (fun edge member => calls edge (List.mem_cons_of_mem _ member))
      refine ⟨later.1, ?_⟩
      intro value present
      rcases List.mem_cons.mp present with rfl | tail
      · exact own.2
      · exact later.2 value tail
termination_by edges.length

/-- Actual projection follows its structural input route to an annotated result. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project path value before result after) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (stored : MuStored valid before)
    (route : TypePath valid path value) : MuStored valid after ∧ Annotated valid result := by
  induction route generalizing before result after with
  | annotated path value annotated =>
      exact SourceCurrentHereditaryProjection.node valid actual semantic available closed stored annotated
  | @ordinary index path entry edges depth free children ih =>
      cases actual with
      | ordinary projected combined =>
          have facts := semantic.ready.semantic.1.normal.facts
          have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
          have rowClosed := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
          have calls : ∀ edge ∈ edges, ∀ child,
              select edge.children index = some child → NodeResult valid path child := by
            intro edge member child found current output final project ready present childClosed currentStore
            exact ih edge member child found project ready present childClosed currentStore
          have localRows := rows_from_calls valid projected semantic resident rowClosed stored calls
          have physical := SourceEqualityProjectionEffects.rows projected semantic resident rowClosed
          exact SourceCurrentHereditaryProjection.union valid combined physical.2.1
            physical.2.2.1 physical.2.2.2 localRows.1 localRows.2
      | recursive recursive _ _ => cases recursive

/-- Ordered row calls use only routes for their selected actual children. -/
theorem rows [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)}
    {results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : ProjectRows path index edges before results after) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (stored : MuStored valid before)
    (routes : ∀ edge ∈ edges, ∀ child,
      select edge.children index = some child → TypePath valid path child) :
    MuStored valid after ∧ ∀ value ∈ results, Annotated valid value := by
  apply rows_from_calls valid actual semantic resident closed stored
  intro edge member child found current output final project ready available childClosed currentStore
  exact node valid project ready available childClosed currentStore (routes edge member child found)

/-- The actual forest read consumes an input certificate rather than a future result law. -/
theorem forest [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {path : List Int} {values : List (Value Symbol Guard)}
    {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Forest path values before result after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) (stored : MuStored valid before)
    (route : ForestPath valid path values) : MuStored valid after ∧ Annotated valid result := by
  cases actual with
  | root combined =>
      exact SourceCurrentHereditaryProjection.union valid combined semantic available closed stored route
  | missing => exact ⟨stored, .empty⟩
  | selected found projected =>
      exact node valid projected semantic (available _ (select_member found))
        (closed _ (select_member found)) stored (route _ found)

end MicroCFTA.SourceCurrentHereditaryTypePaths
