import MicroCFTA.InternedFreshOrdinaryConstruction
import MicroCFTA.InternedNestedConstructionGrowth
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReservations

/-!
# Initial syntax bounds for repaired nested constructor allocation

The budget counts all three possible binder callbacks. Each callback also
pays for root normalization. The bound applies to every actual outcome,
including pending readback. It needs no successful construction premise.
-/
namespace MicroCFTA.InternedFreshOrdinaryAllocationBudget
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedFreshOrdinaryConstruction
open SourceCurrentAllocatedFiniteOrdinaryReservations
variable {Symbol Guard : Type}

mutual
/-- Count possible node allocations from the original constructor syntax. -/
def nodeBudget : Syntax Symbol Guard → Nat
  | .empty | .var _ => 0
  | .node rows => rowNodes rows + 1
  | .union values => manyNodes values + 1
  | .binder _ body => 3 * nodeBudget body + 4
termination_by expression => sizeOf expression

/-- Sum node allocations over the original ordered children. -/
def manyNodes : List (Syntax Symbol Guard) → Nat
  | [] => 0
  | first :: rest => nodeBudget first + manyNodes rest
termination_by expressions => sizeOf expressions

/-- Raw edge work does not allocate a node. -/
def rowNodes : List (EdgeSyntax Symbol Guard) → Nat
  | [] => 0
  | .mk _ _ children :: rest => manyNodes children + rowNodes rest
termination_by expressions => sizeOf expressions
end

mutual
/-- Count possible edge allocations from the original constructor syntax. -/
def edgeBudget : Syntax Symbol Guard → Nat
  | .empty | .var _ => 0
  | .node rows => rowEdges rows
  | .union values => manyEdges values
  | .binder _ body => 3 * edgeBudget body
termination_by expression => sizeOf expression

/-- Sum edge allocations over the original ordered children. -/
def manyEdges : List (Syntax Symbol Guard) → Nat
  | [] => 0
  | first :: rest => edgeBudget first + manyEdges rest
termination_by expressions => sizeOf expressions

/-- Every original raw edge adds one possible edge allocation. -/
def rowEdges : List (EdgeSyntax Symbol Guard) → Nat
  | [] => 0
  | .mk _ _ children :: rest => manyEdges children + 1 + rowEdges rest
termination_by expressions => sizeOf expressions
end

private abbrev Bound (before after : State Symbol Guard) (nodes edges : Nat) : Prop :=
  after.nodes.next ≤ before.nodes.next + nodes ∧ after.edges.next ≤ before.edges.next + edges

private theorem bound_refl (state : State Symbol Guard) : Bound state state 0 0 := by
  constructor <;> omega

private theorem bound_trans {before middle after : State Symbol Guard} {n m e f : Nat}
    (first : Bound before middle n e) (last : Bound middle after m f) : Bound before after (n + m) (e + f) := by
  constructor <;> omega

private theorem bind_bound (outcome : Outcome Symbol Guard A)
    (next : A → State Symbol Guard → Outcome Symbol Guard B) (before : State Symbol Guard)
    (nodes edges laterNodes laterEdges : Nat) (first : Bound before outcome.state nodes edges)
    (later : ∀ value state, Bound state (next value state).state laterNodes laterEdges) :
    Bound before (outcome.bind next).state (nodes + laterNodes) (edges + laterEdges) := by
  cases outcome with
  | pending key state => exact ⟨by dsimp [Outcome.bind, Outcome.state] at *; omega,
      by dsimp [Outcome.bind, Outcome.state] at *; omega⟩
  | done value state => exact bound_trans first (later value state)

private theorem bind_done_state (outcome : Outcome Symbol Guard A) (next : A → B) :
    (outcome.bind fun value state => .done (next value) state).state = outcome.state := by
  cases outcome <;> rfl

section Execution
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem node_bound (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) :
    Bound state (run (makeNode edges) state).2 1 0 := by
  have actual := makeNode_next edges state
  exact ⟨actual.1, by omega⟩

private theorem edge_bound (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard))
    (state : State Symbol Guard) : Bound state (run (makeEdge symbol guard children) state).2 0 1 := by
  have actual := makeEdge_next symbol guard children state
  exact ⟨by omega, actual.2⟩

private theorem raw_node_bound (key : InternedBinderProtocol.NodeKey)
    (identify : Interned InternedBinderProtocol.NodeKey → Value Symbol Guard) (state : State Symbol Guard) :
    Bound state (nodeStep key identify state).2 1 0 := by
  have actual := nodeStep_next key identify state
  split at actual <;> constructor <;> omega

private theorem union_bound (values : List (Value Symbol Guard)) (state : State Symbol Guard) :
    Bound state (run (makeUnion values) state).2 1 0 := by
  unfold makeUnion
  split
  · constructor <;> simp only [run] <;> omega
  · constructor <;> simp only [run] <;> omega
  · split
    · exact node_bound _ _
    · exact raw_node_bound _ _ state

private theorem filter_bound (name : InternedBinderProtocol.Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) : Bound state (run (withoutSelfReference name value) state).2 1 0 := by
  cases value <;> simp only [withoutSelfReference]
  case union entry members depth free =>
    split
    · exact union_bound _ _
    · constructor <;> simp only [run] <;> omega
  all_goals constructor <;> simp only [run] <;> omega

private theorem request_bound (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : InternedBinderProtocol.Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (nodes edges : Nat)
    (callbacks : ∀ name current, Bound current (callback name current).state nodes edges) :
    Bound state (request smart depth ordinary callback state).state (nodes + 1) edges := by
  unfold request
  dsimp only
  split
  · split <;> dsimp only [Outcome.state] <;> constructor <;> omega
  · have reserved := intern_next state.nodes (muKey depth ordinary)
    have step : Bound state {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2} 1 0 := by
      split at reserved <;> constructor <;> dsimp only <;> omega
    have body := callbacks (.interned (Cache.intern state.nodes (muKey depth ordinary)).1.identity)
      {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2}
    have total := bound_trans step body
    cases actual : callback (.interned (Cache.intern state.nodes (muKey depth ordinary)).1.identity)
        {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2} with
    | pending key after =>
        simpa only [actual, Outcome.bind, Outcome.state, Nat.add_comm 1 nodes, Nat.zero_add] using total
    | done value after =>
        simpa only [actual, Outcome.bind, Outcome.state, Nat.add_comm 1 nodes, Nat.zero_add] using total

mutual
/-- Every actual repaired source outcome fits the initial syntax budget. -/
theorem build_bound (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) :
    (build expression environment state).state.nodes.next ≤ state.nodes.next + nodeBudget expression ∧
      (build expression environment state).state.edges.next ≤ state.edges.next + edgeBudget expression := by
  cases expression with
  | empty | var index => exact bound_refl _
  | node rows =>
      rw [build, nodeBudget, edgeBudget]
      simpa only [Nat.add_zero] using bind_bound _ _ state _ _ 1 0 (buildEdges_bound rows environment state) (fun values after => node_bound values after)
  | union values =>
      rw [build, nodeBudget, edgeBudget]
      simpa only [Nat.add_zero] using bind_bound _ _ state _ _ 1 0 (buildMany_bound values environment state) (fun values after => union_bound values after)
  | binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value after => work (withoutSelfReference name value) after
      have callbackBound : ∀ name current, Bound current (callback name current).state (nodeBudget body + 1) (edgeBudget body) := by
        intro name current
        simpa only [Nat.add_zero] using bind_bound _ _ current _ _ 1 0 (build_bound body (.reference name :: environment) current)
          (fun value after => filter_bound name value after)
      rw [build, nodeBudget, edgeBudget]
      change Bound state ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary).state _ _
      have actual := bind_bound (callback .depth state) _ state (nodeBudget body + 1) (edgeBudget body)
        ((nodeBudget body + 1) + ((nodeBudget body + 1) + 1)) (edgeBudget body + edgeBudget body)
        (callbackBound .depth state) (fun depth afterDepth =>
          bind_bound (callback (.uninterned (ordinaryLevel depth)) afterDepth) _ afterDepth
            (nodeBudget body + 1) (edgeBudget body) ((nodeBudget body + 1) + 1) (edgeBudget body)
            (callbackBound _ _) (fun ordinary afterOrdinary => request_bound smart depth ordinary callback afterOrdinary
              (nodeBudget body + 1) (edgeBudget body) callbackBound))
      constructor <;> dsimp only [Bound] at actual ⊢ <;> omega
termination_by sizeOf expression

/-- Ordered children retain their initial summed bound at success or pending. -/
theorem buildMany_bound (expressions : List (Syntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) :
    (buildMany expressions environment state).state.nodes.next ≤ state.nodes.next + manyNodes expressions ∧
      (buildMany expressions environment state).state.edges.next ≤ state.edges.next + manyEdges expressions := by
  cases expressions with
  | nil => exact bound_refl _
  | cons first rest =>
      rw [buildMany, manyNodes, manyEdges]
      exact bind_bound _ _ state _ _ _ _ (build_bound first environment state) (fun value after => by
        simpa only [bind_done_state] using buildMany_bound rest environment after)
termination_by sizeOf expressions

/-- Original rows pay for each raw edge and every nested child construction. -/
theorem buildEdges_bound (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) :
    (buildEdges expressions environment state).state.nodes.next ≤ state.nodes.next + rowNodes expressions ∧
      (buildEdges expressions environment state).state.edges.next ≤ state.edges.next + rowEdges expressions := by
  cases expressions with
  | nil => exact bound_refl _
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          rw [buildEdges, rowNodes, rowEdges]
          have actual := bind_bound (buildMany children environment state) _ state (manyNodes children) (manyEdges children)
            (0 + rowNodes rest) (1 + rowEdges rest) (buildMany_bound children environment state) (fun values after =>
              bind_bound (work (makeEdge symbol guard values) after) _ after 0 1 (rowNodes rest) (rowEdges rest)
                (edge_bound symbol guard values after) (fun edge final => by
                  simpa only [bind_done_state] using buildEdges_bound rest environment final))
          constructor <;> dsimp only [Bound] at actual ⊢ <;> omega
termination_by sizeOf expressions
end
end Execution
end MicroCFTA.InternedFreshOrdinaryAllocationBudget
