import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequiredProfile
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOccurrences
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace

/-!
# Actual required-path requests from original occurrences

Each selected child uses its own original occurrence budget.
Each retained row adds one edge request after its child calls.
Each visited ordinary node adds at most one node request after its rows.
Rejected rows and unselected children consume no additional Work.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequiredReservations
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryReservations
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
local notation "O" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.node
local notation "ORows" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.rows
local notation "OChildren" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.children
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

private def Budget (before after : State Symbol Guard) (counts : Nat × Nat) : Prop :=
  ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ counts.1 ∧ edgeRequests requests ≤ counts.2

private theorem budget_refl (state : State Symbol Guard) (counts : Nat × Nat) : Budget state state counts :=
  ⟨[], .refl _, Nat.zero_le _, Nat.zero_le _⟩

private theorem budget_trans {before middle after : State Symbol Guard} {first last total : Nat × Nat}
    (earlier : Budget before middle first) (later : Budget middle after last)
    (nodes : first.1 + last.1 ≤ total.1) (edges : first.2 + last.2 ≤ total.2) : Budget before after total := by
  obtain ⟨left, firstTrace, firstNodes, firstEdges⟩ := earlier
  obtain ⟨right, lastTrace, lastNodes, lastEdges⟩ := later
  refine ⟨left ++ right, .trans firstTrace lastTrace, ?_, ?_⟩
  · rw [nodeRequests_append]; omega
  · rw [edgeRequests_append]; omega

private theorem budget_mono {before after : State Symbol Guard} {first last : Nat × Nat}
    (actual : Budget before after first) (nodes : first.1 ≤ last.1) (edges : first.2 ≤ last.2) : Budget before after last := by
  obtain ⟨requests, trace, firstNodes, firstEdges⟩ := actual
  exact ⟨requests, trace, Nat.le_trans firstNodes nodes, Nat.le_trans firstEdges edges⟩

private theorem node_work (edges : List (EdgeValue Symbol Guard)) (before after : State Symbol Guard)
    (value : Value Symbol Guard) (built : run (makeNode edges) before = (value, after)) : Budget before after (1, 0) := by
  refine ⟨observe (makeNode edges) before, ?_, ?_, ?_⟩
  · simpa only [built] using Trace.work before (makeNode edges)
  · have counted := (makeNode_requests edges before).1
    split at counted <;> omega
  · exact Nat.le_of_eq (makeNode_requests edges before).2

private theorem edge_work (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (before after : State Symbol Guard) (value : EdgeValue Symbol Guard)
    (built : run (makeEdge symbol guard values) before = (value, after)) : Budget before after (0, 1) := by
  refine ⟨observe (makeEdge symbol guard values) before, ?_, ?_, ?_⟩
  · simpa only [built] using Trace.work before (makeEdge symbol guard values)
  · simp [makeEdge_observe, nodeRequests]
  · simp [makeEdge_observe, edgeRequests]

private def NodeResult (value : Value Symbol Guard) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → Available before value → DNode value → Budget before after (O value)

private def ChildrenResult (values : List (Value Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → Values before values → DChildren values → Budget before after (OChildren values)

private def RowsResult (edges : List (EdgeValue Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → Edges before edges → DRows edges → Budget before after (ORows edges)

private theorem counted :
    (∀ needed (value : Value Symbol Guard) before result after,
      RequireNode needed value before result after → NodeResult value before after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) before results after,
      RequireChildren entries index values before results after → ChildrenResult values before after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      RequireRows entries edges before results after → RowsResult edges before after) := by
  have identityCase : ∀ {value : Value Symbol Guard} {state}, NodeResult value state state := by
    intro value state _ _ _; exact budget_refl _ _
  have emptyCase : ∀ {entries : List (Int × Needed)} {state}, entries ≠ [] →
      NodeResult (.empty : Value Symbol Guard) state state := by
    intro entries state _; exact identityCase
  have ordinaryCase : ∀ {entries edges before rebuilt middle value after entry depth free}, entries ≠ [] →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before rebuilt middle →
      run (makeNode rebuilt) middle = (value, after) → RowsResult edges before middle →
      NodeResult (.node entry edges depth free) before after := by
    intro entries edges before rebuilt middle value after entry depth free _ _ built ih semantic available domain
    have earlier := ih semantic
      (resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident) domain.rows
    exact budget_trans earlier (node_work rebuilt middle after value built) (by simp [SourceCurrentAllocatedFiniteOrdinaryOccurrences.node]; omega)
      (by simp [SourceCurrentAllocatedFiniteOrdinaryOccurrences.node])
  have recursiveCase : ∀ {entries original before exposed middle result after}, entries ≠ [] →
      Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      RequireNode (Symbol := Symbol) (Guard := Guard) (.node entries) exposed middle result after →
      NodeResult exposed middle after → NodeResult original before after := by
    intro entries original before exposed middle result after _ recursive _ _ _ _ _ domain
    cases domain <;> cases recursive
  have nilChildren : ∀ {state}, ChildrenResult ([] : List (Value Symbol Guard)) state state := by
    intro state _ _ _; exact budget_refl _ _
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values before results after →
      ChildrenResult values before after → ChildrenResult (value :: values) before after := by
    intro entries values before results after value index _ _ ih semantic available domain
    have earlier := ih semantic (fun child member => available child (List.mem_cons_of_mem _ member))
      (SourceCurrentAllocatedFiniteOrdinaryDomain.Children.of_members _
        (fun child member => domain.member child (List.mem_cons_of_mem _ member)))
    exact budget_mono earlier (Nat.le_add_left _ _) (Nat.le_add_left _ _)
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some needed →
      RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result middle →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values middle results after →
      NodeResult value before middle → ChildrenResult values middle after → ChildrenResult (value :: values) before after := by
    intro entries needed value before result middle values results after index _ first _ firstIH restIH semantic available domain
    have firstDomain := domain.member value List.mem_cons_self
    have firstAvailable := available value List.mem_cons_self
    have earlier := firstIH semantic firstAvailable firstDomain
    have physical := SourceCurrentAllocatedFiniteOrdinaryRequired.node first semantic firstAvailable firstDomain
    have later := restIH physical.2.1
      (fun child member => physical.1.available child (available child (List.mem_cons_of_mem _ member)))
      (SourceCurrentAllocatedFiniteOrdinaryDomain.Children.of_members _
        (fun child member => domain.member child (List.mem_cons_of_mem _ member)))
    exact budget_trans earlier later (Nat.le_refl _) (Nat.le_refl _)
  have nilRows : ∀ {state}, RowsResult ([] : List (EdgeValue Symbol Guard)) state state := by
    intro state _ _ _; exact budget_refl _ _
  have rejectedCase : ∀ {entries edge edges before results after}, fits (.node entries) edge.children.length = false →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after →
      RowsResult edges before after → RowsResult (edge :: edges) before after := by
    intro entries edge edges before results after _ _ ih semantic resident domain
    have earlier := ih semantic (fun edge member => resident edge (List.mem_cons_of_mem _ member))
      (SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.of_members _
        (fun edge member => domain.member edge (List.mem_cons_of_mem _ member)))
    exact budget_mono earlier (Nat.le_add_left _ _) (Nat.le_add_left _ _)
  have keptCase : ∀ {entries edge before values middle result afterEdge edges results after},
      fits (.node entries) edge.children.length = true →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      RequireRows entries edges afterEdge results after → ChildrenResult edge.children before middle →
      RowsResult edges afterEdge after → RowsResult (edge :: edges) before after := by
    intro entries edge before values middle result afterEdge edges results after fit children built _ childrenIH restIH semantic resident domain
    have edgeDomain := domain.member edge List.mem_cons_self
    have edgeResident := resident edge List.mem_cons_self
    have childrenAvailable : Values before edge.children := fun child member =>
      semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge edgeResident child member
    have earlier := childrenIH semantic childrenAvailable edgeDomain
    have firstGraph : RequireRows entries [edge] before [result] afterEdge := .kept fit children built .nil
    have physical := SourceCurrentAllocatedFiniteOrdinaryRequired.rows firstGraph semantic
      (fun row member => by
        have same := List.mem_singleton.mp member
        subst row
        exact edgeResident)
      (.cons edgeDomain .nil)
    have later := restIH physical.2.1
      (fun row member => edge_grows before afterEdge physical.1.growth row (resident row (List.mem_cons_of_mem _ member)))
      (SourceCurrentAllocatedFiniteOrdinaryDomain.Rows.of_members _
        (fun row member => domain.member row (List.mem_cons_of_mem _ member)))
    have firstBudget : Budget before afterEdge (SourceCurrentAllocatedFiniteOrdinaryOccurrences.edge edge) := by
      cases edge with
      | mk entry originals =>
          exact budget_trans earlier (edge_work _ _ values middle afterEdge result built)
            (by simp [SourceCurrentAllocatedFiniteOrdinaryOccurrences.edge, EdgeValue.children])
            (by simp [SourceCurrentAllocatedFiniteOrdinaryOccurrences.edge, EdgeValue.children]; omega)
    exact budget_trans firstBudget later (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨?_, ?_, ?_⟩
  · intro needed value before result after actual
    exact RequireNode.rec (motive_1 := fun _ value before _ after _ => NodeResult value before after)
      (motive_2 := fun _ _ values before _ after _ => ChildrenResult values before after)
      (motive_3 := fun _ edges before _ after _ => RowsResult edges before after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries index values before results after actual
    exact RequireChildren.rec (motive_1 := fun _ value before _ after _ => NodeResult value before after)
      (motive_2 := fun _ _ values before _ after _ => ChildrenResult values before after)
      (motive_3 := fun _ edges before _ after _ => RowsResult edges before after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries edges before results after actual
    exact RequireRows.rec (motive_1 := fun _ value before _ after _ => NodeResult value before after)
      (motive_2 := fun _ _ values before _ after _ => ChildrenResult values before after)
      (motive_3 := fun _ edges before _ after _ => RowsResult edges before after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual

/-- Actual required-node requests fit all original literal occurrences. -/
theorem node {needed : Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before)
    (available : Available before value) (domain : DNode value) :
    ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ (O value).1 ∧ edgeRequests requests ≤ (O value).2 ∧
      after.nodes.next ≤ before.nodes.next + (O value).1 ∧ after.edges.next ≤ before.edges.next + (O value).2 := by
  obtain ⟨requests, trace, nodes, edges⟩ := counted.1 _ _ _ _ _ actual semantic available domain
  have supplies := trace.next_le
  exact ⟨requests, trace, nodes, edges, by omega, by omega⟩

/-- Actual child requests fit the complete original forest occurrence counts. -/
theorem children {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (actual : RequireChildren entries index values before results after)
    (semantic : SemanticReady before) (available : Values before values) (domain : DChildren values) :
    ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ (OChildren values).1 ∧ edgeRequests requests ≤ (OChildren values).2 ∧
      after.nodes.next ≤ before.nodes.next + (OChildren values).1 ∧ after.edges.next ≤ before.edges.next + (OChildren values).2 := by
  obtain ⟨requests, trace, nodes, edges⟩ := counted.2.1 _ _ _ _ _ _ actual semantic available domain
  have supplies := trace.next_le
  exact ⟨requests, trace, nodes, edges, by omega, by omega⟩

/-- Actual retained rows count each child call and literal edge constructor. -/
theorem rows {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireRows entries edges before results after) (semantic : SemanticReady before)
    (resident : Edges before edges) (domain : DRows edges) :
    ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ (ORows edges).1 ∧ edgeRequests requests ≤ (ORows edges).2 ∧
      after.nodes.next ≤ before.nodes.next + (ORows edges).1 ∧ after.edges.next ≤ before.edges.next + (ORows edges).2 := by
  obtain ⟨requests, trace, nodes, edgeCount⟩ := counted.2.2 _ _ _ _ _ actual semantic resident domain
  have supplies := trace.next_le
  exact ⟨requests, trace, nodes, edgeCount, by omega, by omega⟩

/-- Literal requireAll completion derives request and supply bounds from its original forest. -/
theorem requireAll_done (fuel readFuel : Nat) (paths : List (List Int))
    (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (semantic : SemanticReady before) (available : Values before values) (domain : DChildren values) :
    ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ (OChildren values).1 ∧ edgeRequests requests ≤ (OChildren values).2 ∧
      after.nodes.next ≤ before.nodes.next + (OChildren values).1 ∧ after.edges.next ≤ before.edges.next + (OChildren values).2 := by
  have actual := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr ⟨fuel, readFuel, done⟩
  cases compiled : build paths with
  | node entries =>
      simp only [compiled] at actual
      exact children actual semantic available domain

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequiredReservations
