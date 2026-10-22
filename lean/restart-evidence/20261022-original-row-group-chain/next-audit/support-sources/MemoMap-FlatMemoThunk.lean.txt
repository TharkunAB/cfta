import MicroCFTA.FlatMemoPublication

/-!
# Typed memo thunk publication and observation

The table stores a thunk identity before its request is evaluated. The cell
keeps the original request through evaluation and completion. This model
records logical observations. It does not specify GHC black-hole scheduling,
exception handling, array primitives, or memory barriers.
-/
namespace MicroCFTA.FlatMemoThunk
open Cache

/-- A published thunk can be suspended, under evaluation, or complete. -/
inductive Status (Value : Type) where
  | suspended
  | evaluating
  | returned (value : Value)

/-- A thunk retains its original request in every evaluation phase. -/
structure Cell (Request Value : Type) where
  request : Request
  status : Status Value

/-- The effective table stores logical thunk identities. -/
structure State (Key Request Value : Type) where
  table : Table Key Nat
  cells : Table Nat (Cell Request Value)
  next : Nat

/-- The initial table has no published or allocated thunk. -/
def empty : State Key Request Value := ⟨fun _ => none, fun _ => none, 0⟩

/-- Every table entry identifies its original request and an allocated cell. -/
structure Valid (keyOf : Request → Key → Prop) (good : Cell Request Value → Prop)
    (state : State Key Request Value) : Prop where
  bounded : ∀ handle cell, state.cells handle = some cell → handle < state.next
  linked : ∀ key handle, state.table key = some handle →
    ∃ cell, state.cells handle = some cell ∧ keyOf cell.request key
  checked : ∀ handle cell, state.cells handle = some cell → good cell

/-- An empty table has no supplied result or request assumptions. -/
theorem empty_valid (keyOf : Request → Key → Prop) (good : Cell Request Value → Prop) :
    Valid keyOf good empty := by
  constructor <;> intros <;> contradiction

/-- Retained source facts can strengthen the cell interpretation without table effects. -/
theorem Valid.map (state : State Key Request Value) (keyOf : Request → Key → Prop)
    (first second : Cell Request Value → Prop) (valid : Valid keyOf first state)
    (retained : ∀ cell, first cell → second cell) : Valid keyOf second state :=
  ⟨valid.bounded, valid.linked, fun handle cell stored => retained cell (valid.checked handle cell stored)⟩

/-- A hit returns the original thunk. A miss publishes a suspended request. -/
def lookupOrInsert [DecidableEq Key] (key : Key) (request : Request) (state : State Key Request Value) :
    Nat × State Key Request Value :=
  match state.table key with
  | some handle => (handle, state)
  | none => (state.next, ⟨put state.table key state.next,
      put state.cells state.next ⟨request, .suspended⟩, state.next + 1⟩)

/-- A published key cannot replace its original request with a later candidate. -/
theorem lookup_hit [DecidableEq Key] (key : Key) (request : Request) (state : State Key Request Value)
    (handle : Nat) (stored : state.table key = some handle) :
    lookupOrInsert key request state = (handle, state) := by
  simp only [lookupOrInsert, stored]

/-- Miss publication installs the original suspended request before evaluation. -/
theorem lookup_miss [DecidableEq Key] (key : Key) (request : Request) (state : State Key Request Value)
    (missing : state.table key = none) :
    (lookupOrInsert key request state).1 = state.next ∧
    (lookupOrInsert key request state).2.table key = some state.next ∧
    (lookupOrInsert key request state).2.cells state.next = some ⟨request, .suspended⟩ := by
  simp [lookupOrInsert, missing, put]

/-- Publication retains every earlier key and thunk identity. -/
theorem lookup_extends [DecidableEq Key] (key : Key) (request : Request) (state : State Key Request Value) :
    Extends state.table (lookupOrInsert key request state).2.table := by
  cases found : state.table key with
  | some handle => simpa only [lookupOrInsert, found] using extends_refl state.table
  | none =>
    intro other handle stored
    have different : other ≠ key := by intro same; subst other; rw [found] at stored; cases stored
    simpa only [lookupOrInsert, found, put, ite_eq_right different] using stored

/-- Publication preserves checked cells and allocates a fresh suspended cell. -/
theorem lookup_valid [DecidableEq Key] (key : Key) (request : Request) (state : State Key Request Value)
    (keyOf : Request → Key → Prop) (good : Cell Request Value → Prop)
    (valid : Valid keyOf good state) (requestKey : keyOf request key) (suspended : good ⟨request, .suspended⟩) :
    Valid keyOf good (lookupOrInsert key request state).2 := by
  cases found : state.table key with
  | some handle => simpa only [lookupOrInsert, found] using valid
  | none =>
    simp only [lookupOrInsert, found]
    constructor
    · intro handle cell stored
      change handle < state.next + 1
      by_cases same : handle = state.next
      · subst handle
        omega
      · have old : state.cells handle = some cell := by simpa only [put, ite_eq_right same] using stored
        have := valid.bounded handle cell old
        omega
    · intro other handle stored
      by_cases same : other = key
      · subst other
        have handles : state.next = handle := by simpa [put] using stored
        subst handle
        exact ⟨⟨request, .suspended⟩, by simp [put], requestKey⟩
      · have old : state.table other = some handle := by simpa only [put, ite_eq_right same] using stored
        obtain ⟨cell, present, agrees⟩ := valid.linked other handle old
        have different : handle ≠ state.next := by have := valid.bounded handle cell present; omega
        exact ⟨cell, by simpa only [put, ite_eq_right different] using present, agrees⟩
    · intro handle cell stored
      by_cases same : handle = state.next
      · subst handle
        have cells : (⟨request, .suspended⟩ : Cell Request Value) = cell := by
          simpa [put] using stored
        subst cell
        exact suspended
      · exact valid.checked handle cell (by simpa only [put, ite_eq_right same] using stored)

/-- Set a phase without changing the request, published key, or allocation count. -/
def setStatus (handle : Nat) (status : Status Value) (state : State Key Request Value) : State Key Request Value :=
  match state.cells handle with
  | none => state
  | some cell => { state with cells := put state.cells handle { cell with status := status } }

/-- A phase change retains the published table and original request. -/
theorem setStatus_cell (handle : Nat) (status : Status Value) (state : State Key Request Value)
    (cell : Cell Request Value) (stored : state.cells handle = some cell) :
    (setStatus handle status state).cells handle = some { cell with status := status } := by
  simp [setStatus, stored, put]

/-- Checked phase changes preserve all published request identities. -/
theorem setStatus_valid (handle : Nat) (status : Status Value) (state : State Key Request Value)
    (keyOf : Request → Key → Prop) (good : Cell Request Value → Prop) (valid : Valid keyOf good state)
    (cell : Cell Request Value) (stored : state.cells handle = some cell) (changed : good { cell with status := status }) :
    Valid keyOf good (setStatus handle status state) := by
  simp only [setStatus, stored]
  constructor
  · intro other value present
    by_cases same : other = handle
    · subst other
      exact valid.bounded handle cell stored
    · exact valid.bounded other value (by simpa only [put, ite_eq_right same] using present)
  · intro key other published
    obtain ⟨original, present, agrees⟩ := valid.linked key other published
    by_cases same : other = handle
    · subst other
      have equal : original = cell := Option.some.inj (present.symm.trans stored)
      subst original
      exact ⟨{ cell with status := status }, by simp [put], agrees⟩
    · exact ⟨original, by simpa only [put, ite_eq_right same] using present, agrees⟩
  · intro other value present
    by_cases same : other = handle
    · subst other
      have equal : { cell with status := status } = value := by
        simpa [put] using present
      subst value
      exact changed
    · exact valid.checked other value (by simpa only [put, ite_eq_right same] using present)

/-- Demand either starts the original request or observes its current phase. -/
inductive Observation (Request Value : Type) where
  | absent
  | evaluate (request : Request)
  | busy
  | ready (value : Value)

/-- Demand starts a suspended thunk without removing its published key. -/
def demand (handle : Nat) (state : State Key Request Value) : Observation Request Value × State Key Request Value :=
  match state.cells handle with
  | none => (.absent, state)
  | some cell => match cell.status with
    | .suspended => (.evaluate cell.request, setStatus handle .evaluating state)
    | .evaluating => (.busy, state)
    | .returned value => (.ready value, state)

/-- A recursive demand on a running thunk records a busy observation. -/
theorem demand_busy (handle : Nat) (state : State Key Request Value) (request : Request)
    (stored : state.cells handle = some ⟨request, .evaluating⟩) : demand handle state = (.busy, state) := by
  simp only [demand, stored]

/-- Demand on a completed thunk returns its original value without effects. -/
theorem demand_ready (handle : Nat) (state : State Key Request Value) (request : Request) (value : Value)
    (stored : state.cells handle = some ⟨request, .returned value⟩) : demand handle state = (.ready value, state) := by
  simp only [demand, stored]

/-- Completion changes only a thunk whose original request is under evaluation. -/
def finish (handle : Nat) (value : Value) (state : State Key Request Value) : State Key Request Value :=
  match state.cells handle with
  | some ⟨_, .evaluating⟩ => setStatus handle (.returned value) state
  | _ => state

/-- A completed thunk cannot be replaced by a second completion candidate. -/
theorem finish_ready (handle : Nat) (state : State Key Request Value) (request : Request) (first second : Value)
    (stored : state.cells handle = some ⟨request, .returned first⟩) : finish handle second state = state := by
  simp only [finish, stored]

/-- A recursive request can find the same published thunk before it completes. -/
theorem recursive_pending [DecidableEq Key] (key : Key) (request candidate : Request) (state : State Key Request Value)
    (missing : state.table key = none) :
    let published := (lookupOrInsert key request state).2
    let running := (demand state.next published).2
    (demand state.next published).1 = .evaluate request ∧
    lookupOrInsert key candidate running = (state.next, running) ∧
    demand state.next running = (.busy, running) := by
  simp [lookupOrInsert, missing, demand, setStatus, put]

/-- Completed observations project the pending table to a completed-value table. -/
def completed (state : State Key Request Value) : Table Key Value := fun key => do
  let handle ← state.table key
  let cell ← state.cells handle
  match cell.status with
  | .returned value => some value
  | _ => none

/-- Every projected result comes from a complete cell with the original key. -/
theorem completed_spec (state : State Key Request Value) (keyOf : Request → Key → Prop)
    (good : Cell Request Value → Prop) (valid : Valid keyOf good state) (key : Key) (value : Value)
    (stored : completed state key = some value) :
    ∃ request, keyOf request key ∧ good ⟨request, .returned value⟩ := by
  cases published : state.table key with
  | none => simp [completed, published] at stored
  | some handle =>
    obtain ⟨cell, present, agrees⟩ := valid.linked key handle published
    have checked := valid.checked handle cell present
    cases cell with
    | mk request status =>
      cases status with
      | suspended | evaluating => simp [completed, published, present] at stored
      | returned result =>
        have equal : result = value := by simpa [completed, published, present] using stored
        subst result
        exact ⟨request, agrees, checked⟩

end MicroCFTA.FlatMemoThunk
