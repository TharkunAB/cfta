import MicroCFTA.EnumerationCPSDescent

/-!
# Batched edge enumeration through the source CPS interface

The inherited maximum-child check runs before fresh equality variables are
allocated. Each child receives the inherited obligations followed by the new
obligations. Residual constraints retain the complete constructed fragment.
-/

namespace MicroCFTA.EnumerationCPSBatchedEdge

open Language Fragments EnumerationCPSChecked EnumerationCPSState EnumerationCPSDescent

variable {Symbol Guard : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Source child traversal reads each precomputed bucket at its child index. -/
def childActions (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat)
    (inherited added : List EnumerationState.Suspended) (nodes : List Nat) : Action Symbol Guard (List (Fragment Symbol)) :=
  let buckets := batch (batch (fun _ => []) inherited) added
  EnumerationCPSState.mapM (fun entry =>
    lift (EnumerationState.enumerateNode graph fuel (buckets entry.2) entry.1)) nodes.zipIdx

/-- The batched traversal preserves all child branch order, states, and errors. -/
theorem childActions_exact (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat)
    (inherited added : List EnumerationState.Suspended) (nodes : List Nat)
    (oldValid : ∀ constraint ∈ inherited, EqualityTrie.Valid constraint.trie)
    (newValid : ∀ constraint ∈ added, EqualityTrie.Valid constraint.trie) :
    Represents (childActions graph fuel inherited added nodes)
      (List.mapM (m := EnumerationState.EnumerateM Symbol Guard)
        (fun entry => EnumerationState.enumerateNode graph fuel
          (EnumerationState.descendScs entry.2 (inherited ++ added)) entry.1) nodes.zipIdx) := by
  apply mapM_exact
  intro entry
  rw [inherited_then_new inherited added oldValid newValid]
  exact lift_exact _

/-- The source records the unchanged constraint together with its complete fragment. -/
def recordResidual (residual : Option Guard) (fragment : Fragment Symbol) : Action Symbol Guard Unit :=
  match residual with
  | none => EnumerationCPSChecked.pure ()
  | some guard => EnumerationCPSChecked.modify fun state =>
      {state with obligations := (guard, fragment) :: state.obligations}

/-- The CPS residual write is exactly the established state-machine write. -/
theorem recordResidual_exact (residual : Option Guard) (fragment : Fragment Symbol) :
    Represents (recordResidual residual fragment) (EnumerationSchedule.recordResidual residual fragment) := by
  cases residual with
  | none => exact pure_exact ()
  | some guard => exact modify_exact _

/-- Finish one edge after its fresh equality variables have been allocated. -/
def tail (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat)
    (inherited added : List EnumerationState.Suspended) (edge : EnumerationState.Edge Symbol Guard) :
    Action Symbol Guard (Fragment Symbol) :=
  bind (childActions graph fuel inherited added edge.children) fun children =>
    let fragment := Fragment.node edge.symbol children
    bind (recordResidual edge.residual fragment) fun _ => EnumerationCPSChecked.pure fragment

/-- The existing per-child edge continuation is the comparison sequence. -/
def modelTail (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat)
    (inherited added : List EnumerationState.Suspended) (edge : EnumerationState.Edge Symbol Guard) :
    EnumerationState.EnumerateM Symbol Guard (Fragment Symbol) := do
  let children ← edge.children.zipIdx.mapM fun entry =>
    EnumerationState.enumerateNode graph fuel (EnumerationState.descendScs entry.2 (inherited ++ added)) entry.1
  let fragment := Fragment.node edge.symbol children
  EnumerationSchedule.recordResidual edge.residual fragment
  Pure.pure fragment

/-- Child batching and residual recording preserve the complete old edge continuation. -/
theorem tail_exact (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat)
    (inherited added : List EnumerationState.Suspended) (edge : EnumerationState.Edge Symbol Guard)
    (oldValid : ∀ constraint ∈ inherited, EqualityTrie.Valid constraint.trie)
    (newValid : ∀ constraint ∈ added, EqualityTrie.Valid constraint.trie) :
    Represents (tail graph fuel inherited added edge) (modelTail graph fuel inherited added edge) := by
  unfold tail modelTail
  apply bind_exact _ _ _ _ (childActions_exact graph fuel inherited added edge.children oldValid newValid)
  intro children
  exact bind_exact _ _ _ _ (recordResidual_exact _ _) (fun _ => pure_exact _)

/-- The source allocation traversal has one fixed result and state for any input state. -/
theorem allocation_bind (tries : List EqualityTrie.Trie)
    (next : List EnumerationState.Suspended → Action Symbol Guard α)
    (before : EnumerationState.State Symbol Guard) (success : α → EnumerationState.State Symbol Guard → Result → Result)
    (fail : EnumerationState.Error → Result → Result) (later : Result) :
    bind (EnumerationCPSState.mapM (fun trie => lift (EnumerationState.suspend trie)) tries) next
      before success fail later =
    next (EnumerationCorrectness.suspendedVars before.counter tries)
      (EnumerationCorrectness.suspendedState tries.length before) success fail later := by
  have exact := mapM_exact (Symbol := Symbol) (Guard := Guard) (fun trie => lift (EnumerationState.suspend trie)) EnumerationState.suspend
    (fun _ => lift_exact _) tries
  have same := congrArg (fun computation : Action Symbol Guard (List EnumerationState.Suspended) =>
    computation before (fun value after rest => next value after success fail rest) fail later) exact
  simpa only [EnumerationCPSChecked.bind, encode, EnumerationCorrectness.suspendMany_exact,
    List.foldr_cons, List.foldr_nil, fold] using same

/-- The current source edge step uses one batch arity guard, one allocation traversal, and its batched tail. -/
def edgeAction (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat)
    (inherited : List EnumerationState.Suspended) (edge : EnumerationState.Edge Symbol Guard) :
    Action Symbol Guard (Fragment Symbol) :=
  bind (EnumerationCPSState.require (arityCheck edge.children.length inherited)) fun _ =>
    bind (EnumerationCPSState.mapM (fun trie => lift (EnumerationState.suspend trie)) edge.equalities) fun added =>
      tail graph fuel inherited added edge

/-- The old finite machine has the same deterministic allocation prefix. -/
theorem old_edge_tail (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat)
    (inherited : List EnumerationState.Suspended) (edge : EnumerationState.Edge Symbol Guard)
    (before : EnumerationState.State Symbol Guard)
    (fits : EnumerationState.arityAllows edge.children.length inherited = true) :
    EnumerationState.enumerateEdge graph (fuel + 1) inherited edge before =
      modelTail graph fuel inherited (EnumerationCorrectness.suspendedVars before.counter edge.equalities) edge
        (EnumerationCorrectness.suspendedState edge.equalities.length before) := by
  rw [EnumerationSchedule.edge_action]
  rw [EnumerationCorrectness.bind_single _ _ before before () (by
    simp only [EnumerationState.require, fits, ite_true]
    rfl)]
  rw [EnumerationCorrectness.bind_single _ _ before
    (EnumerationCorrectness.suspendedState edge.equalities.length before)
    (EnumerationCorrectness.suspendedVars before.counter edge.equalities)
    (EnumerationCorrectness.suspendMany_exact edge.equalities before)]
  rfl

/-- The batched CPS step preserves the whole established edge result at every initial state. -/
theorem edgeAction_exact (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat)
    (inherited : List EnumerationState.Suspended) (edge : EnumerationState.Edge Symbol Guard)
    (oldValid : ∀ constraint ∈ inherited, EqualityTrie.Valid constraint.trie)
    (edgeValid : ∀ trie ∈ edge.equalities, EqualityTrie.Valid trie) :
    Represents (edgeAction graph fuel inherited edge) (EnumerationState.enumerateEdge graph (fuel + 1) inherited edge) := by
  unfold Represents
  funext Result before success fail later
  by_cases fits : EnumerationState.arityAllows edge.children.length inherited = true
  · have fresh := suspendedVars_valid edge.equalities edgeValid before.counter
    have continuation := tail_exact graph fuel inherited
      (EnumerationCorrectness.suspendedVars before.counter edge.equalities) edge oldValid fresh
    have continued := congrArg (fun computation : Action Symbol Guard (Fragment Symbol) =>
      computation (EnumerationCorrectness.suspendedState edge.equalities.length before) success fail later) continuation
    change edgeAction graph fuel inherited edge before success fail later = _
    simp only [edgeAction, arityCheck_exact _ inherited oldValid, EnumerationCPSState.require,
      fits, ite_true, EnumerationCPSChecked.bind, EnumerationCPSChecked.pure]
    have allocated := allocation_bind edge.equalities
      (fun added => tail graph fuel inherited added edge) before success fail later
    simp only [EnumerationCPSChecked.bind] at allocated
    rw [allocated]
    simpa only [encode, old_edge_tail graph fuel inherited edge before fits] using continued
  · have falseFits : EnumerationState.arityAllows edge.children.length inherited = false := by
      cases actual : EnumerationState.arityAllows edge.children.length inherited <;> simp_all
    simp only [edgeAction, arityCheck_exact _ inherited oldValid, EnumerationCPSState.require,
      falseFits, Bool.false_eq_true, ite_false, EnumerationCPSChecked.bind, reject]
    have empty : EnumerationState.enumerateEdge graph (fuel + 1) inherited edge before = [] := by
      rw [EnumerationSchedule.edge_action]
      simp only [EnumerationState.require, falseFits, Bool.false_eq_true, ite_false]
      rfl
    simp [encode, empty]

/-- The bounded source worker retains model fuel errors at size zero. -/
def enumerateEdge (graph : EnumerationState.Graph Symbol Guard) : Nat →
    List EnumerationState.Suspended → EnumerationState.Edge Symbol Guard → Action Symbol Guard (Fragment Symbol)
  | 0, _, _ => failure .fuelExhausted
  | fuel + 1, inherited, edge => edgeAction graph fuel inherited edge

/-- Every bounded batched edge computation preserves the exact established CPS denotation. -/
theorem enumerateEdge_exact (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat)
    (inherited : List EnumerationState.Suspended) (edge : EnumerationState.Edge Symbol Guard)
    (oldValid : ∀ constraint ∈ inherited, EqualityTrie.Valid constraint.trie)
    (edgeValid : ∀ trie ∈ edge.equalities, EqualityTrie.Valid trie) :
    Represents (enumerateEdge graph fuel inherited edge) (EnumerationState.enumerateEdge graph fuel inherited edge) := by
  cases fuel with
  | zero => exact failure_exact .fuelExhausted
  | succ fuel => exact edgeAction_exact graph fuel inherited edge oldValid edgeValid

/-- The actual batch worker has identical ordered results and final states at every bound. -/
theorem enumerateEdge_results (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat)
    (inherited : List EnumerationState.Suspended) (edge : EnumerationState.Edge Symbol Guard)
    (oldValid : ∀ constraint ∈ inherited, EqualityTrie.Valid constraint.trie)
    (edgeValid : ∀ trie ∈ edge.equalities, EqualityTrie.Valid trie)
    (before : EnumerationState.State Symbol Guard) :
    allResults (enumerateEdge graph fuel inherited edge) before =
      EnumerationState.enumerateEdge graph fuel inherited edge before :=
  allResults_exact _ _ (enumerateEdge_exact graph fuel inherited edge oldValid edgeValid) before

/-- The source arity guard rejects before it runs fresh equality allocation or child traversal. -/
theorem arity_rejects_before_allocation (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat)
    (inherited : List EnumerationState.Suspended) (edge : EnumerationState.Edge Symbol Guard)
    (outside : arityCheck edge.children.length inherited = false)
    (before : EnumerationState.State Symbol Guard) :
    allResults (edgeAction graph fuel inherited edge) before = [] := by
  simp [edgeAction, outside, EnumerationCPSState.require, EnumerationCPSChecked.bind, reject, allResults]

end MicroCFTA.EnumerationCPSBatchedEdge
