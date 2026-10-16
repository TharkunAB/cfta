import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOccurrences
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace

/-!
# Actual projection constructor requests from original occurrences

Ordinary reads retain the heap. Each visited ordinary projection adds at
most one node request after its selected child calls. Missing positions
skip those calls. The bound counts all original occurrences conservatively.
No edge constructor occurs in this finite ordinary graph.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionReservations
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceCurrentAllocatedFiniteOrdinaryReservations
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
local notation "O" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.node
local notation "ORows" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.rows
local notation "OChildren" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.children
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Ordinary source union records only its literal final node constructor. -/
theorem union_requests {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {result : Value Symbol Guard} (actual : Union values before result after) (domain : DChildren values) :
    ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ 1 ∧ edgeRequests requests = 0 := by
  cases actual with
  | node read built =>
      rename_i edges middle
      have unchanged := (SourceCurrentAllocatedFiniteOrdinaryProjection.readAll_domain read domain).2
      rw [unchanged] at built
      refine ⟨observe (makeNode edges) before, ?_, ?_, (makeNode_requests edges before).2⟩
      · simpa only [built] using Trace.work before (makeNode edges)
      · have counts := (makeNode_requests edges before).1
        split at counts <;> omega

private def NodeResult (value : Value Symbol Guard) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → Available before value → DNode value →
    ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ (O value).1 ∧ edgeRequests requests = 0

private def RowsResult (edges : List (EdgeValue Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → Edges before edges → DRows edges →
    ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ (ORows edges).1 ∧ edgeRequests requests = 0

private theorem counted :
    (∀ path (value : Value Symbol Guard) before result after,
      Project path value before result after → NodeResult value before after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsResult edges before after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeResult value state state := by
    intro value state _ _ _
    exact ⟨[], .refl _, Nat.zero_le _, rfl⟩
  have emptyCase : ∀ {state}, NodeResult (.empty : Value Symbol Guard) state state := rootCase
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      Union values middle result after → RowsResult edges before middle →
      NodeResult (.node entry edges depth free) before after := by
    intro path index edges before values middle result after entry depth free actual union ih semantic available domain
    have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    obtain ⟨earlier, first, firstCount, firstEdges⟩ := ih semantic resident domain.rows
    have physical := SourceCurrentAllocatedFiniteOrdinaryProjection.rows actual semantic resident domain.rows
    obtain ⟨later, last, lastCount, lastEdges⟩ := union_requests union physical.2.2.2
    refine ⟨earlier ++ later, .trans first last, ?_, ?_⟩
    · rw [nodeRequests_append]
      change nodeRequests earlier + nodeRequests later ≤ 1 + (ORows edges).1
      omega
    · rw [edgeRequests_append, firstEdges, lastEdges]
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeResult exposed middle after → NodeResult original before after := by
    intro original before exposed middle path index result after recursive _ _ _ _ _ domain
    cases domain <;> cases recursive
  have nilCase : ∀ {state}, RowsResult ([] : List (EdgeValue Symbol Guard)) state state := by
    intro state _ _ _
    exact ⟨[], .refl _, Nat.le_refl _, rfl⟩
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsResult edges before after → RowsResult (edge :: edges) before after := by
    intro edge path index edges before results after _ _ ih semantic resident domain
    obtain ⟨requests, trace, nodes, edgeCount⟩ := ih semantic
      (fun edge member => resident edge (List.mem_cons_of_mem _ member))
      (SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.of_members _
        (fun edge member => domain.member edge (List.mem_cons_of_mem _ member)))
    exact ⟨requests, trace, Nat.le_trans nodes (Nat.le_add_left _ _), edgeCount⟩
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeResult child before middle →
      RowsResult edges middle after → RowsResult (edge :: edges) before after := by
    intro edge index child path before result middle edges results after found actual _ firstIH restIH semantic resident domain
    have member := select_member found
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
      (resident edge List.mem_cons_self) child member
    have childDomain := (domain.member edge List.mem_cons_self).member child member
    obtain ⟨earlier, first, firstCount, firstEdges⟩ := firstIH semantic available childDomain
    have physical := SourceCurrentAllocatedFiniteOrdinaryProjection.project actual semantic available childDomain
    obtain ⟨later, last, lastCount, lastEdges⟩ := restIH physical.2.1
      (fun edge present => edge_grows before middle physical.1.growth edge (resident edge (List.mem_cons_of_mem _ present)))
      (SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.of_members _
        (fun edge present => domain.member edge (List.mem_cons_of_mem _ present)))
    have bounded := SourceCurrentAllocatedFiniteOrdinaryOccurrences.edge_child edge child member
    refine ⟨earlier ++ later, .trans first last, ?_, ?_⟩
    · rw [nodeRequests_append]
      change nodeRequests earlier + nodeRequests later ≤
        (SourceCurrentAllocatedFiniteOrdinaryOccurrences.edge edge).1 + (ORows edges).1
      omega
    · rw [edgeRequests_append, firstEdges, lastEdges]
  constructor
  · intro path value before result after actual
    exact Project.rec (motive_1 := fun _ value before _ after _ => NodeResult value before after)
      (motive_2 := fun _ _ edges before _ after _ => RowsResult edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual
  · intro path index edges before results after actual
    exact ProjectRows.rec (motive_1 := fun _ value before _ after _ => NodeResult value before after)
      (motive_2 := fun _ _ edges before _ after _ => RowsResult edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual

/-- Every actual ordinary node projection fits its original occurrence count. -/
theorem project {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project path value before result after) (semantic : SemanticReady before)
    (available : Available before value) (domain : DNode value) :
    ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ (O value).1 ∧ edgeRequests requests = 0 ∧
      after.nodes.next ≤ before.nodes.next + (O value).1 ∧ after.edges.next = before.edges.next := by
  obtain ⟨requests, trace, nodes, edges⟩ := counted.1 _ _ _ _ _ actual semantic available domain
  have supplies := trace.next_le
  have exactCounts := trace.next_exact
  have bounded := reservations_le_requests requests
  exact ⟨requests, trace, nodes, edges, by omega, by omega⟩

/-- Ordered row projection counts only selected original child occurrences. -/
theorem rows {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)}
    {results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : ProjectRows path index edges before results after) (semantic : SemanticReady before)
    (resident : Edges before edges) (domain : DRows edges) :
    ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ (ORows edges).1 ∧ edgeRequests requests = 0 ∧
      after.nodes.next ≤ before.nodes.next + (ORows edges).1 ∧ after.edges.next = before.edges.next := by
  obtain ⟨requests, trace, nodes, edgeCount⟩ := counted.2 _ _ _ _ _ _ actual semantic resident domain
  have supplies := trace.next_le
  have exactCounts := trace.next_exact
  have bounded := reservations_le_requests requests
  exact ⟨requests, trace, nodes, edgeCount, by omega, by omega⟩

/-- Forest projection adds at most one root union to its original child occurrences. -/
theorem forest {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : State Symbol Guard} (actual : Forest path values before result after)
    (semantic : SemanticReady before) (available : Values before values) (domain : DChildren values) :
    ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ 1 + (OChildren values).1 ∧ edgeRequests requests = 0 ∧
      after.nodes.next ≤ before.nodes.next + (1 + (OChildren values).1) ∧ after.edges.next = before.edges.next := by
  have counted : ∃ requests, Trace before after requests ∧
      nodeRequests requests ≤ 1 + (OChildren values).1 ∧ edgeRequests requests = 0 := by
    cases actual with
    | root union =>
        obtain ⟨requests, trace, nodes, edges⟩ := union_requests union domain
        exact ⟨requests, trace, by omega, edges⟩
    | missing => exact ⟨[], .refl _, Nat.zero_le _, rfl⟩
    | selected found body =>
        have member := select_member found
        obtain ⟨requests, trace, nodes, edges⟩ := counted.1 _ _ _ _ _ body semantic
          (available _ member) (domain.member _ member)
        have bounded := (SourceCurrentAllocatedFiniteOrdinaryOccurrences.child_member _ _ member).1
        exact ⟨requests, trace, by omega, edges⟩
  obtain ⟨requests, trace, nodes, edges⟩ := counted
  have supplies := trace.next_le
  have exactCounts := trace.next_exact
  have bounded := reservations_le_requests requests
  exact ⟨requests, trace, nodes, edges, by omega, by omega⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionReservations
