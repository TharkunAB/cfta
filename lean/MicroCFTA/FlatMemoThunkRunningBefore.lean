import MicroCFTA.FlatMemoThunkRunning

/-!
# Original running cells after publication and completion

Publication allocates only a suspended cell. Completion leaves no running
cell at its own handle. Every other running cell after these operations
was already running before them. Demand can add only its selected handle.
-/
namespace MicroCFTA.FlatMemoThunk
open Cache

/-- Publication cannot create a running cell. -/
theorem lookup_running_before [DecidableEq Key] (key : Key) (request : Request) (state : State Key Request Value) :
    Running (lookupOrInsert key request state).2 state := by
  intro handle original running
  cases found : state.table key with
  | some existing => simpa only [lookupOrInsert, found] using running
  | none =>
      by_cases same : handle = state.next
      · subst handle
        simp [lookupOrInsert, found, put] at running
      · simpa only [lookupOrInsert, found, put, ite_eq_right same] using running

/-- A completed demand that observes busy identifies its exact original running cell and unchanged state. -/
theorem demand_busy_before (handle : Nat) (state after : State Key Request Value)
    (busy : demand handle state = (.busy, after)) :
    ∃ request, state.cells handle = some ⟨request, .evaluating⟩ ∧ after = state := by
  cases found : state.cells handle with
  | none => simp only [demand, found] at busy; cases busy
  | some cell =>
      cases cell with
      | mk request status =>
          cases status with
          | suspended | returned value => simp only [demand, found] at busy; cases busy
          | evaluating =>
              have same := Prod.mk.inj (by simpa only [demand, found] using busy)
              exact ⟨request, rfl, same.2.symm⟩

/-- An absent demand identifies an actual absent cell. -/
theorem demand_absent_before (handle : Nat) (state after : State Key Request Value)
    (absent : demand handle state = (.absent, after)) : state.cells handle = none := by
  cases found : state.cells handle with
  | none => rfl
  | some cell =>
      cases cell with
      | mk request status => cases status <;> simp only [demand, found] at absent <;> cases absent

/-- Demand can create a running phase only at its own selected handle. -/
theorem demand_running_before_other (handle other : Nat) (state : State Key Request Value) (request : Request)
    (different : other ≠ handle) (running : (demand handle state).2.cells other = some ⟨request, .evaluating⟩) :
    state.cells other = some ⟨request, .evaluating⟩ := by
  cases found : state.cells handle with
  | none => simpa only [demand, found] using running
  | some cell =>
      cases cell with
      | mk original status =>
          cases status with
          | evaluating | returned value => simpa only [demand, found] using running
          | suspended => simpa only [demand, found, setStatus, put, ite_eq_right different] using running

/-- Completion cannot leave a running cell at the handle it completes. -/
theorem finish_not_running (handle : Nat) (value : Value) (state : State Key Request Value) (request : Request) :
    (finish handle value state).cells handle ≠ some ⟨request, .evaluating⟩ := by
  cases found : state.cells handle with
  | none => simp [finish, found]
  | some cell =>
      cases cell with
      | mk original status => cases status <;> simp [finish, found, setStatus, put]

/-- Completion cannot create a running cell at any handle. -/
theorem finish_running_before (handle : Nat) (value : Value) (state : State Key Request Value) :
    Running (finish handle value state) state := by
  intro other original running
  have different : other ≠ handle := by
    intro same
    subst other
    exact finish_not_running handle value state original running
  cases found : state.cells handle with
  | none => simpa only [finish, found] using running
  | some cell =>
      cases cell with
      | mk request status => cases status <;> simpa only [finish, found, setStatus, put, ite_eq_right different] using running

end MicroCFTA.FlatMemoThunk
