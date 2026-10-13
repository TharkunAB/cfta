import MicroCFTA.EnumerationCPS
import MicroCFTA.EnumerationState

/-!
# Error-preserving CPS interpretation of the bounded enumeration model

The finite model reports execution bounds and invariant failures. Haskell's
ordinary failed branch contributes no result. A separate error continuation
keeps that distinction and preserves its position among successful branches.
The source CPS interface is recovered only on an error-free execution.
-/

namespace MicroCFTA.EnumerationCPSChecked

variable {State Error α β : Type}

/-- The checked protocol adds one continuation for explicit model errors. -/
abbrev Computation (State Error α : Type) := {Result : Type} → State →
  (α → State → Result → Result) → (Error → Result → Result) → Result → Result

/-- The finite ordered result list, with errors at their original positions. -/
abbrev Rows (State Error α : Type) := State → List (Except Error (α × State))

/-- Interpret one finite model result in the two-continuation protocol. -/
def fold (success : α → State → Result → Result) (failure : Error → Result → Result) :
    Except Error (α × State) → Result → Result
  | .ok (value, state), later => success value state later
  | .error error, later => failure error later

/-- Encode the ordered bounded model without changing its error behavior. -/
def encode (rows : Rows State Error α) : Computation State Error α :=
  fun state success failure later => (rows state).foldr (fold success failure) later

/-- Record successes and errors in the same order as the finite model. -/
def allResults (action : Computation State Error α) (state : State) : List (Except Error (α × State)) :=
  action state (fun value state later => .ok (value, state) :: later) (fun error later => .error error :: later) []

/-- Exact representation holds for all success, error, and later continuations. -/
def Represents (action : Computation State Error α) (rows : Rows State Error α) : Prop :=
  @action = @encode State Error α rows

/-- Return one checked value at the current state. -/
def pure (value : α) : Computation State Error α := fun state success _ later => success value state later

/-- Reject one branch without inventing an error result. -/
def reject : Computation State Error α := fun _ _ _ later => later

/-- Report one model error without invoking a value continuation. -/
def failure (error : Error) : Computation State Error α := fun _ _ fail later => fail error later

/-- Preserve branch-local state and all error positions under bind. -/
def bind (action : Computation State Error α) (next : α → Computation State Error β) :
    Computation State Error β :=
  fun state success fail later => action state
    (fun value after rest => next value after success fail rest) fail later

/-- Each checked alternative starts from the same input state. -/
def choice (left right : Computation State Error α) : Computation State Error α :=
  fun state success fail later => left state success fail (right state success fail later)

/-- Execute one total source state operation. -/
def state (change : State → α × State) : Computation State Error α :=
  fun before success _ later => let (value, after) := change before; success value after later

/-- Read the current branch state. -/
def get : Computation State Error State := state fun before => (before, before)

/-- Set only the current branch state. -/
def put (after : State) : Computation State Error Unit := state fun _ => ((), after)

/-- Apply a total update only to the current branch state. -/
def modify (change : State → State) : Computation State Error Unit := state fun before => ((), change before)

/-- Emit finite alternatives with the same initial branch state. -/
def branches (values : List α) : Computation State Error α :=
  fun state success _ later => values.foldr (fun value rest => success value state rest) later

/-- A finite encoding reconstructs every success and every explicit error. -/
theorem allResults_encode (rows : Rows State Error α) (state : State) :
    allResults (encode rows) state = rows state := by
  unfold allResults encode
  dsimp only
  induction rows state with
  | nil => rfl
  | cons first rest ih => cases first <;> simp [fold, ih]

/-- Representation preserves the whole checked result list. -/
theorem allResults_exact (action : Computation State Error α) (rows : Rows State Error α)
    (represented : Represents action rows) (state : State) : allResults action state = rows state := by
  rw [represented]
  exact allResults_encode rows state

/-- Checked pure is the exact StateT/ExceptT/List return operation. -/
theorem pure_represents (value : α) : Represents (pure value : Computation State Error α)
    (fun before => [.ok (value, before)]) := rfl

/-- Rejected branches stay distinct from failed bounded execution. -/
theorem reject_represents : Represents (reject : Computation State Error α) (fun _ => []) := rfl

/-- Each model failure remains observable. -/
theorem failure_represents (error : Error) :
    Represents (failure error : Computation State Error α) (fun _ => [.error error]) := rfl

/-- A state update produces one success with its updated local state. -/
theorem state_represents (change : State → α × State) :
    Represents (state change : Computation State Error α) (fun before => [.ok (change before)]) := rfl

/-- Finite branching preserves alternative order and state copies. -/
theorem branches_represents (values : List α) :
    Represents (branches (State := State) (Error := Error) values)
      (fun state => values.map fun value => .ok (value, state)) := by
  unfold Represents branches encode
  funext Result state success failure later
  simp [List.foldr_map, fold]

/-- List choice and CPS choice preserve the same complete result order. -/
theorem choice_represents (left right : Computation State Error α) (first second : Rows State Error α)
    (leftExact : Represents left first) (rightExact : Represents right second) :
    Represents (choice left right) (fun state => first state ++ second state) := by
  rw [leftExact, rightExact]
  unfold Represents choice encode
  funext Result state success fail later
  simp [List.foldr_append]

/-- The independent state/error/list bind keeps errors and flatMaps successes. -/
def bindRows (first : Rows State Error α) (second : α → Rows State Error β) : Rows State Error β :=
  fun state => (first state).flatMap fun result =>
    match result with
    | .ok (value, after) => second value after
    | .error error => [.error error]

/-- Checked CPS bind preserves complete StateT/ExceptT/List behavior. -/
theorem bind_represents (action : Computation State Error α) (next : α → Computation State Error β)
    (first : Rows State Error α) (second : α → Rows State Error β)
    (initial : Represents action first) (following : ∀ value, Represents (next value) (second value)) :
    Represents (bind action next) (bindRows first second) := by
  have nextExact : next = fun value => @encode State Error β (second value) := funext following
  rw [initial, nextExact]
  unfold Represents bind bindRows encode
  funext Result state success fail later
  simp only [List.foldr_flatMap]
  congr 1
  funext result rest
  cases result <;> rfl

/-- Project successes for support theorems, without claiming errors are ordinary failure. -/
def successes (results : List (Except Error (α × State))) : List (α × State) :=
  results.filterMap fun result => match result with | .ok pair => some pair | .error _ => none

/-- An error-free checked execution requires every result to be successful. -/
def ErrorFree (results : List (Except Error (α × State))) : Prop :=
  ∀ error, .error error ∉ results

/-- No information is lost by the successful projection of an error-free execution. -/
theorem successes_recover (results : List (Except Error (α × State))) (safe : ErrorFree results) :
    (successes results).map Except.ok = results := by
  induction results with
  | nil => rfl
  | cons first rest ih =>
      have tailSafe : ErrorFree rest := fun error present => safe error (List.mem_cons_of_mem _ present)
      cases first with
      | error error => exact False.elim (safe error (by simp))
      | ok pair =>
          change Except.ok pair :: (successes rest).map Except.ok = Except.ok pair :: rest
          rw [ih tailSafe]

/-- A successful projected branch is exactly a successful checked branch. -/
theorem mem_successes (results : List (Except Error (α × State))) (value : α) (state : State) :
    (value, state) ∈ successes results ↔ .ok (value, state) ∈ results := by
  simp only [successes, List.mem_filterMap]
  constructor
  · rintro ⟨result, member, found⟩
    cases result with
    | error error => cases found
    | ok pair => have same := Option.some.inj found; subst pair; exact member
  · intro member
    exact ⟨.ok (value, state), member, rfl⟩

/-- Embed the actual source protocol into the checked interface without adding errors. -/
def ofSource (action : EnumerationCPS.Computation State α) : Computation State Error α :=
  fun state success _ later => action state success later

/-- A represented source program gives exactly an error-free checked program. -/
theorem ofSource_represents (action : EnumerationCPS.Computation State α)
    (rows : EnumerationCPS.Branches State α) (represented : EnumerationCPS.Represents action rows) :
    Represents (ofSource action : Computation State Error α) (fun state => (rows state).map Except.ok) := by
  rw [represented]
  unfold Represents ofSource encode EnumerationCPS.encode
  funext Result state success fail later
  simp [List.foldr_map, fold]

end MicroCFTA.EnumerationCPSChecked
