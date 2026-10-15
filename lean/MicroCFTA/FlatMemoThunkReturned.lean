import MicroCFTA.FlatMemoThunkRunning

/-!
# Retain completed cells and their original requests

Lookup, demand, and completion preserve every earlier returned cell.
A cell specification refers to the original request and complete result.
It does not include replay of the effects that produced the result.
-/
namespace MicroCFTA.FlatMemoThunk
open Cache

/-- A later memo retains every earlier returned value and its original request. -/
def Returned (before after : State Key Request Value) : Prop :=
  ∀ handle request value, before.cells handle = some ⟨request, .returned value⟩ →
    after.cells handle = some ⟨request, .returned value⟩

/-- An unchanged table retains each returned cell. -/
theorem Returned.refl (state : State Key Request Value) : Returned state state := fun _ _ _ stored => stored

/-- Returned-cell retention composes through consecutive states. -/
theorem Returned.trans (first : Returned before middle) (second : Returned middle after) : Returned before after :=
  fun handle request value stored => second handle request value (first handle request value stored)

/-- Fresh publication cannot replace any allocated returned cell. -/
theorem lookup_returned [DecidableEq Key] (key : Key) (request : Request) (state : State Key Request Value)
    (keyOf : Request → Key → Prop) (valid : Valid keyOf (fun _ => True) state) :
    Returned state (lookupOrInsert key request state).2 := by
  intro handle original value stored
  cases found : state.table key with
  | some existing => simpa only [lookupOrInsert, found] using stored
  | none =>
      have different : handle ≠ state.next := by have := valid.bounded handle _ stored; omega
      simpa only [lookupOrInsert, found, put, ite_eq_right different] using stored

/-- Demand cannot reset a returned cell, including the demanded cell itself. -/
theorem demand_returned (handle : Nat) (state : State Key Request Value) : Returned state (demand handle state).2 := by
  intro other original value returned
  cases found : state.cells handle with
  | none => simpa only [demand, found] using returned
  | some cell =>
      cases cell with
      | mk request status =>
          cases status with
          | suspended =>
              have different : other ≠ handle := by
                intro same
                subst other
                have impossible := Option.some.inj (returned.symm.trans found)
                cases impossible
              simpa only [demand, found, setStatus, put, ite_eq_right different] using returned
          | evaluating | returned result => simpa only [demand, found] using returned

/-- Completion cannot overwrite an earlier returned cell. -/
theorem finish_returned (handle : Nat) (value : Value) (state : State Key Request Value) : Returned state (finish handle value state) := by
  intro other original result returned
  cases found : state.cells handle with
  | none => simpa only [finish, found] using returned
  | some cell =>
      cases cell with
      | mk request status =>
          cases status with
          | suspended | returned previous => simpa only [finish, found] using returned
          | evaluating =>
              have different : other ≠ handle := by
                intro same
                subst other
                have impossible := Option.some.inj (returned.symm.trans found)
                cases impossible
              simpa only [finish, found, setStatus, put, ite_eq_right different] using returned

/-- A larger interpretation can retain the same original request links. -/
theorem Valid.keyMap (state : State Key Request Value) (first second : Request → Key → Prop)
    (good : Cell Request Value → Prop) (valid : Valid first good state)
    (retained : ∀ request key, first request key → second request key) : Valid second good state :=
  ⟨valid.bounded, fun key handle stored => by
    obtain ⟨cell, present, checked⟩ := valid.linked key handle stored
    exact ⟨cell, present, retained cell.request key checked⟩, valid.checked⟩

/-- Only returned cells require a relation between the original request and result. -/
def CellSpec (spec : Request → Value → Prop) (cell : Cell Request Value) : Prop :=
  match cell.status with
  | .returned value => spec cell.request value
  | _ => True

/-- Starting a suspended request preserves every established result specification. -/
theorem demand_spec (handle : Nat) (state : State Key Request Value) (keyOf : Request → Key → Prop)
    (spec : Request → Value → Prop) (valid : Valid keyOf (CellSpec spec) state) :
    Valid keyOf (CellSpec spec) (demand handle state).2 := by
  cases found : state.cells handle with
  | none => simpa only [demand, found] using valid
  | some cell =>
      cases cell with
      | mk request status =>
          cases status with
          | evaluating | returned value => simpa only [demand, found] using valid
          | suspended =>
              simp only [demand, found]
              exact setStatus_valid handle .evaluating state _ _ valid _ found trivial

/-- Completion checks the result against the request actually stored in the running cell. -/
theorem finish_spec (handle : Nat) (value : Value) (state : State Key Request Value)
    (keyOf : Request → Key → Prop) (spec : Request → Value → Prop)
    (valid : Valid keyOf (CellSpec spec) state)
    (completed : ∀ request, state.cells handle = some ⟨request, .evaluating⟩ → spec request value) :
    Valid keyOf (CellSpec spec) (finish handle value state) := by
  cases found : state.cells handle with
  | none => simpa only [finish, found] using valid
  | some cell =>
      cases cell with
      | mk request status =>
          cases status with
          | suspended | returned previous => simpa only [finish, found] using valid
          | evaluating =>
              simp only [finish, found]
              exact setStatus_valid handle (.returned value) state _ _ valid _ found (completed request found)

/-- Every actual publication returns the handle stored under that key. -/
theorem lookup_stored [DecidableEq Key] (key : Key) (request : Request) (state : State Key Request Value) :
    (lookupOrInsert key request state).2.table key = some (lookupOrInsert key request state).1 := by
  cases found : state.table key <;> simp [lookupOrInsert, found, put]

/-- A ready demand identifies the original returned cell and leaves the entire memo unchanged. -/
theorem demand_ready_original (handle : Nat) (state : State Key Request Value) (value : Value) (after : State Key Request Value)
    (ready : demand handle state = (.ready value, after)) :
    ∃ original, state.cells handle = some ⟨original, .returned value⟩ ∧ after = state := by
  cases found : state.cells handle with
  | none => simp only [demand, found] at ready; cases ready
  | some cell =>
      cases cell with
      | mk original status =>
          cases status with
          | suspended | evaluating => simp only [demand, found] at ready; cases ready
          | returned result =>
              have same := Prod.mk.inj (by simpa only [demand, found] using ready)
              have values := Observation.ready.inj same.1
              subst result
              exact ⟨original, rfl, same.2.symm⟩

end MicroCFTA.FlatMemoThunk
