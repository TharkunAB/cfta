import MicroCFTA.SourceCurrentConjunctionRowsWorker

/-!
# Suspended projection of one class conjunction

The cursor retains the source forest-major jobs and the completed values
in their original order. Each step calls the existing singleton projection
worker. The first actual Empty result completes the conjunction without
forcing the remaining jobs. Exhaustion canonicalizes the completed values.
Projection faults retain their exact returned physical state.

The complete run recurses on the finite pending job list. It needs no
additional observation allowance. This draft does not define shared cells
or select a worklist consumer. Later requirement sharing remains open.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementPull
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome Job)
open SourceCurrentConjunctionRequirements (canonical isEmpty)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard

/-- A continuation stores the pending source jobs and their completed prefix. -/
structure Cursor (Symbol Formula : Type) where
  pending : List (SourceCurrentConjunctionRowsWorker.Job Symbol Formula)
  collected : List (Value Symbol (SourceSymbolicIndex.Constraint Formula))

/-- A step returns a continuation or the completed canonical conjunction. -/
inductive Event (Symbol Formula : Type) where
  | more (next : Cursor Symbol Formula)
  | complete (nodes : List (Value Symbol (SourceSymbolicIndex.Constraint Formula)))

/-- Prepare the literal source jobs without executing a projection. -/
def start (forests : List (List Node)) (paths : EqualityNormalize.Class) : Cursor Symbol Formula :=
  ⟨SourceCurrentConjunctionCompletionReads.jobs forests paths, []⟩

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Read the sole result of the actual singleton projection worker. -/
def projection (p h : Nat) (job : Job Symbol Formula) (before : Physical Symbol Formula) :
    Outcome Symbol Formula Node :=
  (SourceCurrentConjunctionRowsWorker.projections p h [job] before).bind fun values after =>
    .done (values.headD .empty) after

/-- The singleton worker always returns exactly the value read by this view. -/
theorem projection_singleton (p h : Nat) (job : Job Symbol Formula) (before : Physical Symbol Formula) :
    (projection p h job before).bind (fun value after => .done [value] after) =
      SourceCurrentConjunctionRowsWorker.projections p h [job] before := by
  rcases job with ⟨forest, path⟩
  cases actual : SourceEqualityProjectionWorker.forest p h (path.map Int.ofNat) forest before.heap <;>
    simp only [projection, SourceCurrentConjunctionRowsWorker.projections, actual,
      Outcome.bind, List.headD_cons]

/-- Successful and failed projections leave equality operations unchanged. -/
theorem projection_equality (p h : Nat) (job : Job Symbol Formula) (before : Physical Symbol Formula) :
    (projection p h job before).state.equality = before.equality := by
  rcases job with ⟨forest, path⟩
  cases actual : SourceEqualityProjectionWorker.forest p h (path.map Int.ofNat) forest before.heap <;>
    simp only [projection, SourceCurrentConjunctionRowsWorker.projections, actual,
      Outcome.bind, Outcome.state]

/-- Execute at most one pending projection and stop at its actual Empty result. -/
def step (p h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula) :
    Outcome Symbol Formula (Event Symbol Formula) :=
  match cursor.pending with
  | [] => .done (.complete (canonical cursor.collected)) before
  | job :: rest =>
      (projection p h job before).bind fun value after =>
        if isEmpty value then .done (.complete [.empty]) after
        else .done (.more ⟨rest, cursor.collected ++ [value]⟩) after

/-- End of the jobs canonicalizes the completed prefix without another read. -/
theorem step_nil (p h : Nat) (collected : List Node) (before : Physical Symbol Formula) :
    step p h ⟨[], collected⟩ before = .done (.complete (canonical collected)) before := rfl

/-- A failed projection returns its exact fault and state before the suffix. -/
theorem step_failed (p h : Nat) (job : Job Symbol Formula) (rest : List (Job Symbol Formula))
    (collected : List Node) (before after : Physical Symbol Formula)
    (fault : SourceCurrentConjunctionRowsWorker.Fault)
    (actual : projection p h job before = .failed fault after) :
    step p h ⟨job :: rest, collected⟩ before = .failed fault after := by
  simp only [step, actual, Outcome.bind]

/-- The first actual Empty completes without executing any remaining job. -/
theorem step_empty (p h : Nat) (job : Job Symbol Formula) (rest : List (Job Symbol Formula))
    (collected : List Node) (before after : Physical Symbol Formula)
    (actual : projection p h job before = .done .empty after) :
    step p h ⟨job :: rest, collected⟩ before = .done (.complete [.empty]) after := by
  simp only [step, actual, Outcome.bind, isEmpty, ite_true]

/-- A nonempty result appends one value and suspends the unforced job suffix. -/
theorem step_more (p h : Nat) (job : Job Symbol Formula) (rest : List (Job Symbol Formula))
    (collected : List Node) (before after : Physical Symbol Formula) (value : Node)
    (actual : projection p h job before = .done value after) (nonempty : isEmpty value = false) :
    step p h ⟨job :: rest, collected⟩ before =
      .done (.more ⟨rest, collected ++ [value]⟩) after := by
  simp only [step, actual, Outcome.bind, nonempty, Bool.false_eq_true, ite_false]

private def collect (p h : Nat) : List (Job Symbol Formula) → List Node →
    Physical Symbol Formula → Outcome Symbol Formula (List Node)
  | [], values, before => .done (canonical values) before
  | job :: rest, values, before =>
      (projection p h job before).bind fun value after =>
        if isEmpty value then .done [.empty] after
        else collect p h rest (values ++ [value]) after

/-- Complete the finite pending jobs with the same projection and read bounds. -/
def run (p h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula) :
    Outcome Symbol Formula (List Node) :=
  collect p h cursor.pending cursor.collected before

/-- Start one actual class conjunction in the literal source job order. -/
def classConjunction (p h : Nat) (forests : List (List Node)) (paths : EqualityNormalize.Class)
    (before : Physical Symbol Formula) : Outcome Symbol Formula (List Node) :=
  run p h (start forests paths) before

/-- The finite run is the exact repeated execution of its suspended transition. -/
theorem run_step (p h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula) :
    run p h cursor before =
      (step p h cursor before).bind fun event after =>
        match event with
        | .more next => run p h next after
        | .complete nodes => .done nodes after := by
  rcases cursor with ⟨jobs, collected⟩
  cases jobs with
  | nil => rfl
  | cons job rest =>
      cases actual : projection p h job before with
      | failed fault after => simp only [run, collect, step, actual, Outcome.bind]
      | done value after =>
          simp only [run, collect, step, actual, Outcome.bind]
          split <;> rfl

/-- Exhaustion returns the same canonical prefix and the identical physical state. -/
theorem run_nil (p h : Nat) (collected : List Node) (before : Physical Symbol Formula) :
    run p h ⟨[], collected⟩ before = .done (canonical collected) before := rfl

/-- Complete execution propagates the exact first failed projection. -/
theorem run_failed (p h : Nat) (job : Job Symbol Formula) (rest : List (Job Symbol Formula))
    (collected : List Node) (before after : Physical Symbol Formula)
    (fault : SourceCurrentConjunctionRowsWorker.Fault)
    (actual : projection p h job before = .failed fault after) :
    run p h ⟨job :: rest, collected⟩ before = .failed fault after := by
  simp only [run, collect, actual, Outcome.bind]

/-- Complete execution returns immediately at the first actual Empty result. -/
theorem run_empty (p h : Nat) (job : Job Symbol Formula) (rest : List (Job Symbol Formula))
    (collected : List Node) (before after : Physical Symbol Formula)
    (actual : projection p h job before = .done .empty after) :
    run p h ⟨job :: rest, collected⟩ before = .done [.empty] after := by
  simp only [run, collect, actual, Outcome.bind, isEmpty, ite_true]

/-- Only a nonempty completed projection enters the literal remaining jobs. -/
theorem run_more (p h : Nat) (job : Job Symbol Formula) (rest : List (Job Symbol Formula))
    (collected : List Node) (before after : Physical Symbol Formula) (value : Node)
    (actual : projection p h job before = .done value after) (nonempty : isEmpty value = false) :
    run p h ⟨job :: rest, collected⟩ before = run p h ⟨rest, collected ++ [value]⟩ after := by
  simp only [run, collect, actual, Outcome.bind, nonempty, Bool.false_eq_true, ite_false]

end MicroCFTA.SourceCurrentConjunctionRequirementPull
