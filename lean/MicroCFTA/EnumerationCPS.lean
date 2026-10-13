import Std

/-!
# The source continuation-passing enumeration operations

These definitions follow `Enumeration.hs`: success receives a value, its
branch state, and the result of all later branches. Choice passes the same
input state to both sides. Bind visits each continuation before later input
branches. The representation theorem preserves the entire ordered list,
including duplicates and final states.

The theorem concerns total finite branch lists and total state operations.
It does not equate Haskell bottoms with a rejected branch or establish the
productivity of an infinite lazy computation.
-/

namespace MicroCFTA.EnumerationCPS

variable {State α β : Type}

/-- The source rank-polymorphic continuation protocol. -/
abbrev Computation (State α : Type) :=
  {Result : Type} → State → (α → State → Result → Result) → Result → Result

/-- The ordered StateT/list denotation. -/
abbrev Branches (State α : Type) := State → List (α × State)

/-- The source allBranches continuation records each final branch state. -/
def allBranches (action : Computation State α) (state : State) : List (α × State) :=
  action state (fun value after later => (value, after) :: later) []

/-- Inject a finite list denotation into the source continuation interface. -/
def encode (action : Branches State α) : Computation State α :=
  fun state success later => (action state).foldr (fun pair rest => success pair.1 pair.2 rest) later

/-- Finite representation requires agreement for every continuation and later result. -/
def Represents (action : Computation State α) (denotation : Branches State α) : Prop :=
  @action = @encode State α denotation

/-- Return one value without changing its branch state. -/
def pure (value : α) : Computation State α := fun state success later => success value state later

/-- A failed branch contributes no value and does not alter later branches. -/
def failure : Computation State α := fun _ _ later => later

/-- Choice visits the left branch first, with separate input-state copies. -/
def choice (left right : Computation State α) : Computation State α :=
  fun state success later => left state success (right state success later)

/-- Bind supplies each continuation with the state of its own input branch. -/
def bind (action : Computation State α) (next : α → Computation State β) : Computation State β :=
  fun state success later => action state (fun value after rest => next value after success rest) later

/-- Functor mapping transforms only returned values. -/
def map (transform : α → β) (action : Computation State α) : Computation State β :=
  fun state success later => action state (fun value => success (transform value)) later

/-- Applicative application follows the source function-major branch order. -/
def ap (functions : Computation State (α → β)) (arguments : Computation State α) : Computation State β :=
  fun state success later => functions state
    (fun transform after rest => arguments after (fun value => success (transform value)) rest) later

/-- The state primitive unpacks the completed pair before success. -/
def state (change : State → α × State) : Computation State α :=
  fun before success later => let (value, after) := change before; success value after later

/-- Read the current branch state. -/
def get : Computation State State := state fun before => (before, before)

/-- Replace only the current branch state. -/
def put (after : State) : Computation State Unit := state fun _ => ((), after)

/-- Update only the current branch state. -/
def modify (change : State → State) : Computation State Unit := state fun before => ((), change before)

/-- Source branches is a right fold over alternatives with the same input state. -/
def branches (values : List α) : Computation State α :=
  fun state success later => values.foldr (fun value rest => success value state rest) later

/-- Recording an encoded finite list returns exactly that list. -/
theorem allBranches_encode (action : Branches State α) (state : State) :
    allBranches (encode action) state = action state := by
  simp [allBranches, encode]

/-- A represented source computation preserves every result and final state in order. -/
theorem allBranches_exact (action : Computation State α) (denotation : Branches State α)
    (represented : Represents action denotation) (state : State) :
    allBranches action state = denotation state := by
  rw [represented]
  exact allBranches_encode denotation state

/-- Pure has exactly one branch at the unchanged state. -/
theorem pure_represents (value : α) : Represents (pure value : Computation State α)
    (fun before => [(value, before)]) := rfl

/-- Source failure is the empty branch list. -/
theorem failure_represents : Represents (failure : Computation State α) (fun _ => []) := rfl

/-- The state primitive has one completed output pair. -/
theorem state_represents (change : State → α × State) :
    Represents (state change) (fun before => [change before]) := rfl

/-- The direct branches fold is the ordered list of unchanged-state alternatives. -/
theorem branches_represents (values : List α) :
    Represents (branches (State := State) values) (fun state => values.map (fun value => (value, state))) := by
  unfold Represents branches encode
  funext Result state success later
  simp [List.foldr_map]

/-- Choice concatenates the two branch lists without passing left state to the right. -/
theorem choice_represents (left right : Computation State α) (first second : Branches State α)
    (leftExact : Represents left first) (rightExact : Represents right second) :
    Represents (choice left right) (fun state => first state ++ second state) := by
  rw [leftExact, rightExact]
  unfold Represents choice encode
  funext Result state success later
  simp [List.foldr_append]

/-- CPS bind equals ordered StateT/list flatMap, including each local state. -/
theorem bind_represents (action : Computation State α) (next : α → Computation State β)
    (first : Branches State α) (second : α → Branches State β)
    (initial : Represents action first) (following : ∀ value, Represents (next value) (second value)) :
    Represents (bind action next)
      (fun state => (first state).flatMap fun pair => second pair.1 pair.2) := by
  have nextExact : next = fun value => @encode State β (second value) := funext following
  rw [initial, nextExact]
  unfold Represents bind encode
  funext Result state success later
  simp [List.foldr_flatMap]

/-- Functor mapping preserves the final state of every branch. -/
theorem map_represents (transform : α → β) (action : Computation State α) (denotation : Branches State α)
    (represented : Represents action denotation) :
    Represents (map transform action)
      (fun state => (denotation state).map fun pair => (transform pair.1, pair.2)) := by
  rw [represented]
  unfold Represents map encode
  funext Result state success later
  simp [List.foldr_map]

/-- Applicative application uses the same ordered state-dependent product as StateT. -/
theorem ap_represents (functions : Computation State (α → β)) (arguments : Computation State α)
    (functionRows : Branches State (α → β)) (argumentRows : Branches State α)
    (functionExact : Represents functions functionRows) (argumentExact : Represents arguments argumentRows) :
    Represents (ap functions arguments)
      (fun state => (functionRows state).flatMap fun function =>
        (argumentRows function.2).map fun argument => (function.1 argument.1, argument.2)) := by
  rw [functionExact, argumentExact]
  unfold Represents ap encode
  funext Result state success later
  simp [List.foldr_flatMap, List.foldr_map]

/-- A failed branch's state updates do not affect the later alternative. -/
theorem failed_state_is_local (before changed : State) :
    allBranches (choice (bind (put changed) (fun _ => failure)) get) before = [(before, before)] := rfl

/-- Choice gives both branches the original state despite a successful left update. -/
theorem successful_state_is_local (before changed : State) :
    allBranches (choice (bind (put changed) (fun _ => get)) get) before =
      [(changed, changed), (before, before)] := rfl

/-- The source runner can append an arbitrary later branch list unchanged. -/
theorem run_with_later (action : Computation State α) (rows : Branches State α)
    (represented : Represents action rows) (state : State) (later : List (α × State)) :
    action state (fun value after rest => (value, after) :: rest) later = rows state ++ later := by
  have same := congrArg (fun computation : Computation State α =>
    computation state (fun value after rest => (value, after) :: rest) later) represented
  simpa [encode] using same

/-- A finite left branch contributes its full prefix before an arbitrary later computation. -/
theorem choice_prefix (left right : Computation State α) (rows : Branches State α)
    (represented : Represents left rows) (state : State) :
    (allBranches (choice left right) state).take (rows state).length = rows state := by
  unfold allBranches choice
  dsimp only
  rw [run_with_later left rows represented]
  simp

/-- The source fail method ignores its message and uses the empty alternative. -/
def fail (_message : String) : Computation State α := failure

/-- Failed pattern matches retain no result and no branch-state changes. -/
theorem fail_represents (message : String) :
    Represents (fail (State := State) (α := α) message) (fun _ => []) := rfl

/-- Get returns the current state without changing it. -/
theorem get_represents : Represents (get : Computation State State)
    (fun state => [(state, state)]) := rfl

/-- Put changes only the final state of its own branch. -/
theorem put_represents (after : State) : Represents (put after)
    (fun _ => [((), after)]) := rfl

/-- Modify applies one total function to its branch state. -/
theorem modify_represents (change : State → State) : Represents (modify change)
    (fun before => [((), change before)]) := rfl

end MicroCFTA.EnumerationCPS
