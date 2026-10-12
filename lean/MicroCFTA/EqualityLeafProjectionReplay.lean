import MicroCFTA.EqualityLeafProjectionWorkerCompletion

/-!
# Common-cache replay of recursive child edits

Parent normalization compares child results in a common completed cache.
The finite request sequence constructs this cache. Each original request
then returns its exact result without allocation, including repeated input
occurrences that the canonical source node has merged.
-/
namespace MicroCFTA.EqualityLeafProjectionWorkers
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open EqualityLeafProjectionSyntax EqualityLeafProjectionPhysical

/-- Complete a finite list of physical requests in its given source occurrence order. -/
def sequence : List (Work Symbol Guard Result) → Work Symbol Guard (List Result)
  | [] => .pure []
  | first :: rest => first.bind fun value => (sequence rest).bind fun values => .pure (value :: values)

/-- Safe recursive child requests derive safety for the complete finite sequence. -/
theorem sequence_safe (requests : List (Work Symbol Guard Result)) (safe : ∀ request ∈ requests, Safe request) :
    Safe (sequence requests) := by
  induction requests with
  | nil => trivial
  | cons first rest ih => exact safe_bind _ _ (safe first (by simp)) (fun _ =>
      safe_bind _ _ (ih (fun request member => safe request (by simp [member]))) (fun _ => trivial))

/-- Completion produces a common cache where every constituent request replays
without allocation. Its ordered result list is the same list of readbacks. -/
theorem sequence_completed [DecidableEq (EdgeKey Symbol Guard)]
    (requests : List (Work Symbol Guard Result)) (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state) :
    let result := run (sequence requests) state
    result.1 = requests.map (fun request => (run request result.2).1) ∧
      ∀ request ∈ requests, run request result.2 = ((run request result.2).1, result.2) := by
  induction requests generalizing state with
  | nil => exact ⟨rfl, by simp⟩
  | cons first rest ih =>
      let head := run first state
      let tail := run (sequence rest) head.2
      have headValid : InternedConstructorTemplates.Valid head.2 := (InternedConstructorTemplates.run_correct first state valid).1
      have checked : tail.1 = rest.map (fun request => (run request tail.2).1) ∧
          ∀ request ∈ rest, run request tail.2 = ((run request tail.2).1, tail.2) := ih head.2 headValid
      have growth : Grows head.2 tail.2 := (InternedConstructorTemplates.run_correct (sequence rest) head.2 headValid).2
      have repeated := replay first state tail.2 valid growth
      have same := congrArg (fun result : Result × State Symbol Guard => result.1) repeated
      simp only [sequence, run_bind, run]
      change head.1 :: tail.1 = (first :: rest).map (fun request => (run request tail.2).1) ∧
        ∀ request ∈ first :: rest, run request tail.2 = ((run request tail.2).1, tail.2)
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, same, checked.1]
        rfl
      · intro request member
        rcases List.mem_cons.mp member with equal | present
        · subst request
          exact repeated.trans (congrArg (fun value => (value, tail.2)) same.symm)
        · exact checked.2 request present

/-- A successful recursive worker exposes its complete value for the parent rebuild. -/
def workerValue [DecidableEq (EdgeKey Symbol Guard)] (work : Work Symbol Guard (Option (Value Symbol Guard)))
    (state : State Symbol Guard) : Value Symbol Guard := (run work state).1.getD .empty

/-- The default is unreachable for completed ordinary workers in the common cache. -/
theorem workerValue_exact [DecidableEq (EdgeKey Symbol Guard)]
    (requests : List (Work Symbol Guard (Option (Value Symbol Guard)))) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (work : Work Symbol Guard (Option (Value Symbol Guard)))
    (member : work ∈ requests) (returns : Returns work (run (sequence requests) state).2) :
    run work (run (sequence requests) state).2 =
      (some (workerValue work (run (sequence requests) state).2), (run (sequence requests) state).2) := by
  have replayed := (sequence_completed requests state valid).2 work member
  obtain ⟨value, present⟩ := returns
  simpa only [workerValue, present, Option.getD_some] using replayed

/-- The actual finite edit result supplies the positional child transformation. -/
def editedChild [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target)) (state : State Symbol Guard) (index : Nat) (value : Value Symbol Guard) : Value Symbol Guard :=
  workerValue (edit meet (descendEdits edits index) value) state

/-- Required-path child results use the same original positional suffixes. -/
def requiredChild [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (state : State Symbol Guard) (index : Nat) (value : Value Symbol Guard) : Value Symbol Guard :=
  workerValue (require (descend paths index) value) state

/-- Physical recursive child editing derives the parent adapter's empty-node premise. -/
theorem editedChild_empty [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target)) (state : State Symbol Guard) (index : Nat) : editedChild meet edits state index .empty = .empty := by
  simp only [editedChild, workerValue, edit_empty, run, Option.getD_some]

/-- Physical recursive requirements derive the same empty-node premise. -/
theorem requiredChild_empty [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (state : State Symbol Guard) (index : Nat) : requiredChild paths state index .empty = .empty := by
  simp only [requiredChild, workerValue, require_empty, run, Option.getD_some]

/-- Recursive edit results instantiate physical parent normalization.
The child cache is explicit; the completed request theorem below constructs it. -/
theorem edited_parent_readback [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target)) (childState before state : State Symbol Guard)
    (beforeCoherent : Coherent before) (linked : Linked before) (coherent : Coherent state)
    (edges : List (EdgeValue Symbol Guard)) (resident : ∀ edge ∈ edges, EdgeResident before edge) :
    let change := editedChild meet edits childState
    let after := (run (rebuildMany change edges) state).2
    makeNode (edges.map (rebuild after change)) =
      makeNode ((nodeEdges (run (makeNode edges) before).1).map (rebuild after change)) :=
  completed_edit_readback before state beforeCoherent linked coherent edges resident
    (editedChild meet edits childState) (editedChild_empty meet edits childState)

/-- Actual recursive required-path results instantiate the filtered parent equation. -/
theorem required_parent_readback [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (childState before state : State Symbol Guard)
    (beforeCoherent : Coherent before) (linked : Linked before) (coherent : Coherent state)
    (edges : List (EdgeValue Symbol Guard)) (resident : ∀ edge ∈ edges, EdgeResident before edge) :
    let change := requiredChild paths childState
    let after := (run (rebuildMany change edges) state).2
    makeNode ((edges.filter (fun edge => fits paths edge.children.length)).map (rebuild after change)) =
      makeNode (((nodeEdges (run (makeNode edges) before).1).filter
        (fun edge => fits paths edge.children.length)).map (rebuild after change)) :=
  completed_require_readback before state beforeCoherent linked coherent paths edges resident
    (requiredChild paths childState) (requiredChild_empty paths childState)

/-- Enumerate each original child occurrence with its source index. -/
def indexed (offset : Nat) : List α → List (Nat × α)
  | [] => []
  | value :: rest => (offset, value) :: indexed (offset + 1) rest

/-- Indexing retains only original child payloads. -/
theorem indexed_member (offset index : Nat) (values : List α) (value : α)
    (member : (index, value) ∈ indexed offset values) : value ∈ values := by
  induction values generalizing offset with
  | nil => simp [indexed] at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | present
      · exact List.mem_cons.mpr (Or.inl (Prod.mk.inj same).2)
      · exact List.mem_cons_of_mem first (ih (offset + 1) present)

/-- Retained original rows enumerate every recursive positional child request. -/
def childRequests (request : Nat → Value Symbol Guard → Work Symbol Guard Result)
    (edges : List (EdgeValue Symbol Guard)) : List (Work Symbol Guard Result) :=
  edges.flatMap fun edge => (indexed 0 edge.children).map fun position => request position.1 position.2

/-- Every original child occurrence has its actual worker in the finite request sequence. -/
theorem childRequests_member (request : Nat → Value Symbol Guard → Work Symbol Guard Result)
    (edges : List (EdgeValue Symbol Guard)) (edge : EdgeValue Symbol Guard) (member : edge ∈ edges)
    (index : Nat) (child : Value Symbol Guard) (position : (index, child) ∈ indexed 0 edge.children) :
    request index child ∈ childRequests request edges :=
  List.mem_flatMap.mpr ⟨edge, member, List.mem_map.mpr ⟨(index, child), position, rfl⟩⟩

/-- Local request safety certifies the exact generated occurrence sequence. -/
theorem childRequests_safe (request : Nat → Value Symbol Guard → Work Symbol Guard Result)
    (safe : ∀ index child, Safe (request index child)) (edges : List (EdgeValue Symbol Guard)) :
    ∀ work ∈ childRequests request edges, Safe work := by
  intro work member
  obtain ⟨edge, _, present⟩ := List.mem_flatMap.mp member
  obtain ⟨⟨index, child⟩, _, rfl⟩ := List.mem_map.mp present
  exact safe index child

/-- Every ordinary child request returns its exact result in the common completed cache. -/
theorem childRequests_completed [DecidableEq (EdgeKey Symbol Guard)]
    (request : Nat → Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (returns : ∀ index child, Ordinary child → ∀ state, Returns (request index child) state)
    (edges : List (EdgeValue Symbol Guard)) (ordinary : ∀ edge ∈ edges, ∀ child ∈ edge.children, Ordinary child)
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) (index : Nat) (child : Value Symbol Guard)
    (position : (index, child) ∈ indexed 0 edge.children) :
    let final := (run (sequence (childRequests request edges)) state).2
    run (request index child) final = (some (workerValue (request index child) final), final) :=
  workerValue_exact (childRequests request edges) state valid (request index child)
    (childRequests_member request edges edge member index child position)
    (returns index child (ordinary edge member child (indexed_member 0 index edge.children child position)) _)

/-- Actual child execution and actual parent rebuilding discharge both the
completed-child and output-residency premises for physical edit normalization. -/
theorem edited_parent_completed [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (meetSafe : ∀ target value, Safe (meet target value)) (edits : List (Path × Target))
    (before state : State Symbol Guard) (beforeCoherent : Coherent before) (linked : Linked before)
    (coherent : Coherent state) (edges : List (EdgeValue Symbol Guard))
    (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (ordinary : ∀ edge ∈ edges, ∀ child ∈ edge.children, Ordinary child) :
    let request := fun index child => edit meet (descendEdits edits index) child
    let children := (run (sequence (childRequests request edges)) state).2
    let change := editedChild meet edits children
    let after := (run (rebuildMany change edges) children).2
    makeNode (edges.map (rebuild after change)) =
        makeNode ((nodeEdges (run (makeNode edges) before).1).map (rebuild after change)) ∧
      ∀ edge ∈ edges, ∀ index child, (index, child) ∈ indexed 0 edge.children →
        run (request index child) children = (some (change index child), children) := by
  let request := fun index child => edit meet (descendEdits edits index) child
  let children := (run (sequence (childRequests request edges)) state).2
  have safe : ∀ work ∈ childRequests request edges, Safe work :=
    childRequests_safe request (fun index child => edit_safe meet meetSafe _ child) edges
  have childrenCoherent : Coherent children := InternedErasedEdgeReplay.run_coherent _ state
    (sequence_safe _ safe) coherent
  refine ⟨edited_parent_readback meet edits children before children beforeCoherent linked childrenCoherent edges resident, ?_⟩
  intro edge member index child position
  exact childRequests_completed request (fun index child ordinary current => edit_returns meet _ child ordinary current)
    edges ordinary state coherent.valid edge member index child position

/-- Required-path filtering uses actual completed child requirements and
retains the source's original-arity selection before parent rebuilding. -/
theorem required_parent_completed [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (before state : State Symbol Guard) (beforeCoherent : Coherent before) (linked : Linked before)
    (coherent : Coherent state) (edges : List (EdgeValue Symbol Guard))
    (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (ordinary : ∀ edge ∈ edges, ∀ child ∈ edge.children, Ordinary child) :
    let selected := edges.filter (fun edge => fits paths edge.children.length)
    let request := fun index (child : Value Symbol Guard) => require (descend paths index) child
    let children := (run (sequence (childRequests request selected)) state).2
    let change := requiredChild paths children
    let after := (run (rebuildMany change edges) children).2
    makeNode ((edges.filter (fun edge => fits paths edge.children.length)).map (rebuild after change)) =
        makeNode (((nodeEdges (run (makeNode edges) before).1).filter
          (fun edge => fits paths edge.children.length)).map (rebuild after change)) ∧
      ∀ edge ∈ selected, ∀ index child, (index, child) ∈ indexed 0 edge.children →
        run (request index child) children = (some (change index child), children) := by
  let selected := edges.filter (fun edge => fits paths edge.children.length)
  let request := fun index (child : Value Symbol Guard) => require (descend paths index) child
  let children := (run (sequence (childRequests request selected)) state).2
  have safe : ∀ work ∈ childRequests request selected, Safe work :=
    childRequests_safe request (fun index child => require_safe _ child) selected
  have childrenCoherent : Coherent children := InternedErasedEdgeReplay.run_coherent _ state
    (sequence_safe _ safe) coherent
  refine ⟨required_parent_readback paths children before children beforeCoherent linked childrenCoherent edges resident, ?_⟩
  intro edge member index child position
  exact childRequests_completed request (fun index child ordinary current => require_returns _ child ordinary current)
    selected (fun edge member => ordinary edge (List.mem_filter.mp member).1) state coherent.valid edge member index child position

end MicroCFTA.EqualityLeafProjectionWorkers
