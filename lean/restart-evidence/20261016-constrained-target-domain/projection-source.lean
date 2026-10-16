import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFinite
import MicroCFTA.SourceEqualityProjectionGraph

/-!
# Finite ordinary structure through actual path projection

Ordinary row reads retain their literal rows and heap. Ordered source union
constructs a node from those rows. Projection follows selected children and
keeps every intermediate physical effect. A domain input cannot select a
recursive head. Guards and equality classes have no restriction.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache (Keeps pure_keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
variable {Symbol Guard : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A domain read returns the literal ordinary rows without a heap effect. -/
theorem read_domain {value : Value Symbol Guard} {before after : State Symbol Guard}
    {edges : List (EdgeValue Symbol Guard)} (trace : Read value before edges after) (domain : DNode value) :
    DRows edges ∧ after = before := by
  cases trace with
  | done fuel completed =>
      cases domain with
      | empty =>
          simp only [MergedFreshOrdinaryExposure.nodeEdges] at completed
          cases completed
          exact ⟨.nil, rfl⟩
      | ordinary rows =>
          simp only [MergedFreshOrdinaryExposure.nodeEdges] at completed
          cases completed
          exact ⟨rows, rfl⟩

/-- Ordered domain reads concatenate their actual rows at the same heap. -/
theorem readAll_domain {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {edges : List (EdgeValue Symbol Guard)} (trace : ReadAll values before edges after) (domain : DChildren values) :
    DRows edges ∧ after = before := by
  induction trace with
  | nil => exact ⟨.nil, rfl⟩
  | @cons value before rows middle values more after first rest ih =>
      cases domain with
      | cons firstDomain restDomain =>
          have firstRows := read_domain first firstDomain
          have restRows := ih restDomain
          refine ⟨SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.of_members _ ?_, restRows.2.trans firstRows.2⟩
          intro edge member
          rcases List.mem_append.mp member with left | right
          · exact firstRows.1.member edge left
          · exact restRows.1.member edge right

/-- Actual source union preserves the finite ordinary domain at its returned heap. -/
theorem union_domain {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {result : Value Symbol Guard} (trace : Union values before result after) (semantic : SemanticReady before)
    (available : Values before values) (domain : DChildren values) : DNode result := by
  cases trace with
  | node read built =>
      have physical := read.verified semantic available (fun value member =>
        SourceCurrentAllocatedFiniteOrdinaryFinite.closed before semantic.ready.semantic.1.normal.facts.coherent
          value (available value member) (domain.member value member))
      have rowDomain := (readAll_domain read domain).1
      have actual := SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode _ _
        physical.2.1.ready.semantic.1.normal.facts.coherent physical.2.1.ready.semantic.1.normal.facts.linked
        physical.2.2.1 rowDomain
      simpa only [built] using actual

private def NodeResult (input : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  SemanticReady before → Available before input → DNode input →
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ DNode result

private def RowsResult (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (results : List (Value Symbol Guard)) (after : State Symbol Guard) : Prop :=
  SemanticReady before → Edges before edges → DRows edges →
    Keeps before after ∧ SemanticReady after ∧ Values after results ∧ DChildren results

private theorem projection :
    (∀ path (value : Value Symbol Guard) before result after,
      Project path value before result after → NodeResult value before result after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsResult edges before results after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeResult value state value state := by
    intro value state semantic available domain
    exact ⟨pure_keeps state semantic.ready, semantic, available, domain⟩
  have emptyCase : ∀ {state}, NodeResult (.empty : Value Symbol Guard) state .empty state := by
    intro state semantic available _
    exact ⟨pure_keeps state semantic.ready, semantic, available, .empty⟩
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      Union values middle result after → RowsResult edges before values middle →
      NodeResult (.node entry edges depth free) before result after := by
    intro path index edges before values middle result after entry depth free _ union ih semantic available domain
    have rows := ih semantic
      (resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident) domain.rows
    have closed := fun value member => SourceCurrentAllocatedFiniteOrdinaryFinite.closed middle
      rows.2.1.ready.semantic.1.normal.facts.coherent value (rows.2.2.1 value member) (rows.2.2.2.member value member)
    have physical := union.verified rows.2.1 rows.2.2.1 closed
    exact ⟨rows.1.trans physical.1, physical.2.1, physical.2.2.1,
      union_domain union rows.2.1 rows.2.2.1 rows.2.2.2⟩
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeResult exposed middle result after → NodeResult original before result after := by
    intro original before exposed middle path index result after recursive _ _ _ _ _ domain
    cases domain <;> cases recursive
  have nilCase : ∀ {state}, RowsResult ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intro state semantic _ _
    exact ⟨pure_keeps state semantic.ready, semantic, (by intro value member; cases member), .nil⟩
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsResult edges before results after → RowsResult (edge :: edges) before results after := by
    intro edge path index edges before results after _ _ ih semantic resident domain
    exact ih semantic (fun edge member => resident edge (List.mem_cons_of_mem _ member))
      (SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.of_members _
        (fun edge member => domain.member edge (List.mem_cons_of_mem _ member)))
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeResult child before result middle →
      RowsResult edges middle results after → RowsResult (edge :: edges) before (result :: results) after := by
    intro edge index child path before result middle edges results after found _ _ firstIH restIH semantic resident domain
    have member := select_member found
    have first := firstIH semantic
      (semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self) child member)
      ((domain.member edge List.mem_cons_self).member child member)
    have rest := restIH first.2.1
      (fun edge present => edge_grows before middle first.1.growth edge (resident edge (List.mem_cons_of_mem _ present)))
      (SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.of_members _
        (fun edge member => domain.member edge (List.mem_cons_of_mem _ member)))
    refine ⟨first.1.trans rest.1, rest.2.1, ?_, .cons first.2.2.2 rest.2.2.2⟩
    intro value present
    rcases List.mem_cons.mp present with rfl | later
    · exact rest.1.available _ first.2.2.1
    · exact rest.2.2.1 value later
  constructor
  · intro path value before result after trace
    exact Project.rec (motive_1 := fun _ value before result after _ => NodeResult value before result after)
      (motive_2 := fun _ _ edges before results after _ => RowsResult edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace
  · intro path index edges before results after trace
    exact ProjectRows.rec (motive_1 := fun _ value before result after _ => NodeResult value before result after)
      (motive_2 := fun _ _ edges before results after _ => RowsResult edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace

/-- Every actual node projection preserves the domain and derives its current physical effects. -/
theorem project {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project path value before result after) (semantic : SemanticReady before)
    (available : Available before value) (domain : DNode value) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ DNode result :=
  projection.1 _ _ _ _ _ trace semantic available domain

/-- Ordered actual row projections return an available domain child forest. -/
theorem rows {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)}
    {results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : ProjectRows path index edges before results after) (semantic : SemanticReady before)
    (resident : Edges before edges) (domain : DRows edges) :
    Keeps before after ∧ SemanticReady after ∧ Values after results ∧ DChildren results :=
  projection.2 _ _ _ _ _ _ trace semantic resident domain

/-- Forest root union and signed child projection retain the same concrete result domain. -/
theorem forest {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : State Symbol Guard} (trace : Forest path values before result after)
    (semantic : SemanticReady before) (available : Values before values) (domain : DChildren values) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ DNode result := by
  cases trace with
  | root union =>
      have physical := union.verified semantic available (fun value member =>
        SourceCurrentAllocatedFiniteOrdinaryFinite.closed before semantic.ready.semantic.1.normal.facts.coherent
          value (available value member) (domain.member value member))
      exact ⟨physical.1, physical.2.1, physical.2.2.1, union_domain union semantic available domain⟩
  | missing => exact ⟨pure_keeps _ semantic.ready, semantic, empty_available _, .empty⟩
  | selected found body => exact project body semantic (available _ (select_member found)) (domain.member _ (select_member found))

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection
