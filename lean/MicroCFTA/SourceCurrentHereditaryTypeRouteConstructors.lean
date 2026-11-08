import MicroCFTA.SourceCurrentHereditaryTypePaths
import MicroCFTA.MergedPhysicalGroupEdges

/-!
# Structural Type routes through actual row constructors

Each output row retains an original guard and all child-forest routes.
Node normalization selects those complete rows. Exact cache readback retains
the selected payloads. No Program symbol or unrelated guard is classified.
-/
namespace MicroCFTA.SourceCurrentHereditaryTypeRouteConstructors
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedFacts InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceEqualityProjectionGraph (select select_member)
open SourceCurrentHereditaryTypePaths (TypePath ForestPath)
variable {Symbol Guard : Type}

/-- Every original structural forest route is retained. -/
def ForestRoutes (valid : Guard → Prop) (originals results : List (Value Symbol Guard)) : Prop :=
  ∀ path, ForestPath valid path originals → ForestPath valid path results

/-- Each output row retains one original guard and the original child routes. -/
def RowRoutes (valid : Guard → Prop) (originals results : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ row ∈ results, ∃ original ∈ originals,
    row.entry.key.constraint = original.entry.key.constraint ∧ ForestRoutes valid original.children row.children

/-- An empty route requires an annotation on the complete input value. -/
theorem route_nil {valid : Guard → Prop} {value : Value Symbol Guard}
    (route : TypePath valid [] value) : Annotated valid value := by
  cases route with
  | annotated path value checked => exact checked

/-- A nonempty ordinary route supplies routes at every selected child. -/
theorem ordinary_children {valid : Guard → Prop} {index : Int} {path : List Int}
    {entry : Interned InternedBinderProtocol.NodeKey} {rows : List (EdgeValue Symbol Guard)}
    {depth : Nat} {free : List InternedBinderProtocol.Reference}
    (route : TypePath valid (index :: path) (.node entry rows depth free)) :
    ∀ row ∈ rows, ∀ child, select row.children index = some child → TypePath valid path child := by
  cases route with
  | annotated own value checked =>
      intro row member child selected
      exact .annotated path child
        ((SourceCurrentHereditaryConstructors.node_edge checked row member).2 child (select_member selected))
  | ordinary children => exact children

/-- Actual node reconstruction retains every route of the original ordinary input. -/
theorem makeNode_routes [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (entry : Interned InternedBinderProtocol.NodeKey) (oldRows : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (newRows : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (resident : Edges state newRows) (routes : RowRoutes valid oldRows newRows) :
    ∀ path, TypePath valid path (.node entry oldRows depth free) →
      TypePath valid path (run (makeNode newRows) state).1 := by
  intro path route
  cases path with
  | nil =>
      have original := route_nil route
      have typed : ∀ row ∈ newRows, SourceCurrentHereditaryConstructors.Edge valid row := by
        intro row member
        obtain ⟨source, included, guard, children⟩ := routes row member
        have annotated := SourceCurrentHereditaryConstructors.node_edge original source included
        constructor
        · rw [guard]; exact annotated.1
        · exact children [] annotated.2
      exact .annotated [] _ (SourceCurrentHereditaryConstructors.makeNode valid newRows state
        facts.coherent facts.linked resident typed)
  | cons index path =>
      have original := ordinary_children route
      have selected : Edges state (canonicalEdges (surviving newRows)) :=
        fun row member => resident row (List.mem_filter.mp (canonicalEdges_member _ row member)).1
      have selectedRoutes : ∀ row ∈ canonicalEdges (surviving newRows),
          ∀ child, select row.children index = some child → TypePath valid path child := by
        intro row member
        obtain ⟨source, included, guard, children⟩ :=
          routes row (List.mem_filter.mp (canonicalEdges_member _ row member)).1
        exact children (index :: path) (original source included)
      unfold makeNode
      dsimp only
      split
      · exact .annotated _ _ .empty
      · rename_i first rest same
        obtain ⟨chosen, readback⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
          (by simpa [InternedNestedProvenance.Edges, same] using selected)
        simp only [run, readback, identifyNode]
        apply TypePath.ordinary
        intro row member child found
        exact selectedRoutes row (by simpa [same] using member) child found

/-- Actual edge readback retains the same guard and every supplied child route. -/
theorem makeEdge_routes [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (original : EdgeValue Symbol Guard) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (available : Values state values) (routes : ForestRoutes valid original.children values) :
    RowRoutes valid [original] [(run (makeEdge original.entry.key.symbol original.entry.key.constraint values) state).1] := by
  intro row member
  have same := List.mem_singleton.mp member
  subst row
  have fields := MergedPhysicalGroupEdges.makeEdge_fields state facts
    original.entry.key.symbol original.entry.key.constraint values available
  refine ⟨original, List.mem_cons_self, fields.2.1, ?_⟩
  simpa only [fields.2.2] using routes

end MicroCFTA.SourceCurrentHereditaryTypeRouteConstructors
