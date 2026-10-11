import MicroCFTA.SymbolicInputScope

/-!
# Stable finite bounds for source state traversals

An eventual result includes the exact final memo tables. Once a bound is
large enough, every larger bound returns the same value and the same state.
Finite traversals combine their recursive bounds without dropping calls.
-/
namespace MicroCFTA.SymbolicDriver

/-- A state computation returns one stable successful result at every sufficiently large fuel. -/
def Eventually (action : Nat → StateT State (Except Failure) Value) (initial : State) : Prop :=
  ∃ bound value finalState, ∀ fuel, bound ≤ fuel → action fuel initial = .ok (value, finalState)

/-- A fixed successful state operation needs no recursive fuel. -/
theorem eventually_constant (action : StateT State (Except Failure) Value) (initial finalState : State) (value : Value)
    (success : action initial = .ok (value, finalState)) : Eventually (fun _ => action) initial :=
  ⟨0, value, finalState, fun _ _ => success⟩

/-- Pure source values have stable outputs and unchanged state. -/
theorem eventually_pure (value : Value) (initial : State) :
    Eventually (fun _ => (pure value : StateT State (Except Failure) Value)) initial :=
  ⟨0, value, initial, fun _ _ => rfl⟩

/-- Stable stateful results compose through the source monadic bind. -/
theorem eventually_bind (first : Nat → StateT State (Except Failure) Input)
    (next : Nat → Input → StateT State (Except Failure) Output) (initial : State)
    (starts : Eventually first initial) (continues : ∀ value state, Eventually (fun fuel => next fuel value) state) :
    Eventually (fun fuel => do let value ← first fuel; next fuel value) initial := by
  obtain ⟨firstBound, value, middle, firstResult⟩ := starts
  obtain ⟨secondBound, output, finalState, nextResult⟩ := continues value middle
  refine ⟨max firstBound secondBound, output, finalState, ?_⟩
  intro fuel bound
  change Except.bind (first fuel initial) (fun (value, state) => next fuel value state) = .ok (output, finalState)
  rw [firstResult fuel (by omega)]
  exact nextResult fuel (by omega)

/-- Stable computations can be followed by any fixed pure value and state update. -/
theorem eventually_post (first : Nat → StateT State (Except Failure) Input)
    (update : Input × State → Output × State) (initial : State) (starts : Eventually first initial) :
    Eventually (fun fuel state => (first fuel state).map update) initial := by
  obtain ⟨bound, value, finalState, stable⟩ := starts
  refine ⟨bound, (update (value, finalState)).1, (update (value, finalState)).2, ?_⟩
  intro fuel larger
  simp only [stable fuel larger, Except.map]

/-- Stable finite state traversals have one common bound and retain every visited action. -/
theorem eventually_mapM (action : Nat → Input → StateT State (Except Failure) Output) (inputs : List Input)
    (total : ∀ input ∈ inputs, ∀ state, Eventually (fun fuel => action fuel input) state) (initial : State) :
    Eventually (fun fuel => inputs.mapM (action fuel)) initial := by
  induction inputs generalizing initial with
  | nil => exact eventually_pure [] initial
  | cons first rest ih =>
      simp only [List.mapM_cons]
      apply eventually_bind _ _ initial (total first (by simp) initial)
      intro head middle
      apply eventually_bind _ _ middle (ih (fun input member => total input (by simp [member])) middle)
      intro tail finalState
      exact eventually_pure (head :: tail) finalState

/-- One source call frame adds one to a sufficient bound. -/
theorem eventually_succ (action body : Nat → StateT State (Except Failure) Value) (initial : State)
    (equation : ∀ fuel, action (fuel + 1) = body fuel) (total : Eventually body initial) : Eventually action initial := by
  obtain ⟨bound, value, finalState, stable⟩ := total
  refine ⟨bound + 1, value, finalState, ?_⟩
  intro fuel larger
  cases fuel with
  | zero => omega
  | succ fuel => rw [equation fuel]; exact stable fuel (by omega)

/-- The actual signed union traversal has a stable result when every generated edge call does. -/
theorem countUnion_eventually [DecidableEq Symbol] (graph : Graph Symbol)
    (action : Nat → Edge Symbol → CountM Symbol Int) (edges : List (Edge Symbol))
    (total : ∀ piece ∈ Symbolic.unionCoefficients (intersectEdge graph) edges, ∀ state,
      Eventually (fun fuel => action fuel piece.1) state) (initial : Counts Symbol) :
    Eventually (fun fuel => countUnion graph (action fuel) edges) initial := by
  unfold countUnion
  apply eventually_bind _ _ initial
  · apply eventually_mapM
    intro piece member state
    apply eventually_bind _ _ state (total piece member state)
    intro count finalState
    exact eventually_pure (piece.2 * count) finalState
  · intro values state
    exact eventually_pure values.sum state

end MicroCFTA.SymbolicDriver
