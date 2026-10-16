import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardConstructors
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionProfile

/-!
# Hereditary guards through actual signed projections

Projection selects original children and unions their returned rows.
The proof follows each supplied graph at its actual intermediate heap.
Every output constraint retains the initial hereditary bound.
This result verifies completed graphs. It does not assert completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardProjection
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceCurrentAllocatedFiniteOrdinaryGuardProfiles
local notation "Guard" => SourceSymbolicIndex.Constraint
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
variable {Symbol Formula : Type}
variable [DecidableEq (EdgeKey Symbol (Guard Formula))]

/-- Actual source union retains each guard from its original finite ordinary forest. -/
theorem union {limit : Limits} {values : List (Value Symbol (Guard Formula))}
    {before after : State Symbol (Guard Formula)} {result : Value Symbol (Guard Formula)}
    (actual : Union values before result after) (semantic : SemanticReady before)
    (available : Values before values) (profile : Children limit values) : Node limit result := by
  cases actual with
  | node read built =>
      obtain ⟨sameRows, sameHeap⟩ := SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.readAll_exact read
        (Children.domain values profile)
      rw [sameRows, sameHeap] at built
      have facts := semantic.ready.semantic.1.normal.facts
      have resident : ∀ edge ∈ values.flatMap nodeEdges, EdgeResident before edge := by
        intro edge member
        obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
        exact resident_edges before facts.linked value (available value present).resident edge included
      have bounded := SourceCurrentAllocatedFiniteOrdinaryGuardConstructors.makeNode _ before
        facts.coherent facts.linked resident
        (SourceCurrentAllocatedFiniteOrdinaryGuardConstructors.flattened_rows values profile)
      simpa only [built] using bounded

private def NodeResult (input : Value Symbol (Guard Formula)) (before : State Symbol (Guard Formula))
    (result : Value Symbol (Guard Formula)) : Prop :=
  ∀ limit, SemanticReady before → Available before input → Node limit input → Node limit result

private def RowsResult (edges : List (EdgeValue Symbol (Guard Formula)))
    (before : State Symbol (Guard Formula)) (results : List (Value Symbol (Guard Formula))) : Prop :=
  ∀ limit, SemanticReady before → Edges before edges → Rows limit edges → Children limit results

private theorem projection :
    (∀ path (value : Value Symbol (Guard Formula)) before result after,
      Project path value before result after → NodeResult value before result) ∧
    (∀ path index (edges : List (EdgeValue Symbol (Guard Formula))) before results after,
      ProjectRows path index edges before results after → RowsResult edges before results) := by
  have rootCase : ∀ {value : Value Symbol (Guard Formula)} {state}, NodeResult value state value := by
    intro value state limit _ _ profile
    exact profile
  have emptyCase : ∀ {state}, NodeResult (.empty : Value Symbol (Guard Formula)) state .empty := by
    intro state limit _ _ _
    trivial
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard Formula) path index edges before values middle →
      Union values middle result after → RowsResult edges before values →
      NodeResult (.node entry edges depth free) before result := by
    intro path index edges before values middle result after entry depth free actual unionTrace ih
      limit semantic available profile
    have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have outputs := ih limit semantic resident profile
    have physical := SourceCurrentAllocatedFiniteOrdinaryProjection.rows actual semantic resident (Rows.domain edges profile)
    exact union unionTrace physical.2.1 physical.2.2.1 outputs
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard Formula) (index :: path) exposed middle result after →
      NodeResult exposed middle result → NodeResult original before result := by
    intro original before exposed middle path index result after recursive _ _ _ limit _ _ profile
    have domain := Node.domain original profile
    cases domain <;> cases recursive
  have nilCase : ∀ {state}, RowsResult ([] : List (EdgeValue Symbol (Guard Formula))) state [] := by
    intro state limit _ _ _
    trivial
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard Formula) path index edges before results after →
      RowsResult edges before results → RowsResult (edge :: edges) before results := by
    intro edge path index edges before results after _ _ ih limit semantic resident profile
    exact ih limit semantic (fun edge member => resident edge (List.mem_cons_of_mem _ member)) profile.2
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard Formula) path child before result middle →
      ProjectRows path index edges middle results after → NodeResult child before result →
      RowsResult edges middle results → RowsResult (edge :: edges) before (result :: results) := by
    intro edge index child path before result middle edges results after found actual _ firstIH restIH
      limit semantic resident profile
    have included := select_member found
    have childBound := Children.member edge.children (Edge.children edge profile.1) child included
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
      (resident edge List.mem_cons_self) child included
    have first := firstIH limit semantic available childBound
    have physical := SourceCurrentAllocatedFiniteOrdinaryProjection.project actual semantic available (Node.domain child childBound)
    have later := restIH limit physical.2.1
      (fun edge member => edge_grows before middle physical.1.growth edge (resident edge (List.mem_cons_of_mem _ member))) profile.2
    exact ⟨first, later⟩
  constructor
  · intro path value before result after actual
    exact Project.rec (motive_1 := fun _ value before result _ _ => NodeResult value before result)
      (motive_2 := fun _ _ edges before results _ _ => RowsResult edges before results)
      rootCase (fun {_ _ _} => emptyCase) ordinaryCase recursiveCase (fun {_ _ _} => nilCase) missingCase selectedCase actual
  · intro path index edges before results after actual
    exact ProjectRows.rec (motive_1 := fun _ value before result _ _ => NodeResult value before result)
      (motive_2 := fun _ _ edges before results _ _ => RowsResult edges before results)
      rootCase (fun {_ _ _} => emptyCase) ordinaryCase recursiveCase (fun {_ _ _} => nilCase) missingCase selectedCase actual

/-- Actual signed node projection retains all initial nested constraint bounds. -/
theorem project {limit : Limits} {path : List Int} {value result : Value Symbol (Guard Formula)}
    {before after : State Symbol (Guard Formula)} (actual : Project path value before result after)
    (semantic : SemanticReady before) (available : Available before value) (profile : Node limit value) :
    Node limit result :=
  projection.1 _ _ _ _ _ actual limit semantic available profile

/-- Ordered row projection retains the same bound at every selected result. -/
theorem rows {limit : Limits} {path : List Int} {index : Int}
    {edges : List (EdgeValue Symbol (Guard Formula))} {results : List (Value Symbol (Guard Formula))}
    {before after : State Symbol (Guard Formula)} (actual : ProjectRows path index edges before results after)
    (semantic : SemanticReady before) (resident : Edges before edges) (profile : Rows limit edges) :
    Children limit results :=
  projection.2 _ _ _ _ _ _ actual limit semantic resident profile

/-- Forest projection retains the same bound through root union and signed selection. -/
theorem forest {limit : Limits} {path : List Int} {values : List (Value Symbol (Guard Formula))}
    {result : Value Symbol (Guard Formula)} {before after : State Symbol (Guard Formula)}
    (actual : Forest path values before result after) (semantic : SemanticReady before)
    (available : Values before values) (profile : Children limit values) : Node limit result := by
  cases actual with
  | root actual => exact union actual semantic available profile
  | missing => trivial
  | selected found actual =>
      have included := select_member found
      exact project actual semantic (available _ included) (Children.member values profile _ included)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardProjection
