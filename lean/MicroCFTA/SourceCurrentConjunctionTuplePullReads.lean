import MicroCFTA.SourceCurrentConjunctionTuplePullProgress
import MicroCFTA.SourceCurrentConjunctionCompletionReads

/-!
# Actual singleton reads in physical cursor transitions

Each transition demands at most one original operand. An extension steps
its inner cursor and returns before reading its own operand. The receipt
records that actual read. Silent transitions retain the physical state.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullReads
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionTuplePull (Cursor Event)
open SourceCurrentConjunctionCompletionReads (Exposures)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

/-- Only seed and nonempty operand-read states demand a physical row read. -/
def requested : Cursor Symbol Formula → Option Node
  | .seed node => some node
  | .extend _ inner => requested inner
  | .readOperand node _ (_ :: _) => some node
  | _ => none

/-- Suspended operand references belong to the original support list. -/
def Supported (support : List Node) : Cursor Symbol Formula → Prop
  | .empty | .seedRows _ => True
  | .seed node => node ∈ support
  | .extend node inner | .readOperand node inner _ | .scanOperand node inner _ _ =>
      node ∈ support ∧ Supported support inner

/-- Syntactic progress retains the literal operand support. -/
theorem next_supported (support : List Node) {cursor next : Cursor Symbol Formula}
    (transition : SourceCurrentConjunctionTuplePullProgress.Next next cursor)
    (supported : Supported support cursor) : Supported support next := by
  revert supported
  induction transition with
  | seed | seedTail => intro _; trivial
  | extendMore _ _ ih | extendYield _ _ _ ih =>
      intro supported
      exact ⟨supported.1, ih supported.2⟩
  | readScan | readReset | scanTail | scanReset => intro supported; exact supported

private theorem fold_supported (support nodes : List Node) (cursor : Cursor Symbol Formula)
    (supported : Supported support cursor) (included : ∀ node ∈ nodes, node ∈ support) :
    Supported support (nodes.foldr Cursor.extend cursor) := by
  induction nodes with
  | nil => exact supported
  | cons node nodes ih =>
      exact ⟨included node List.mem_cons_self,
        ih (fun value member => included value (List.mem_cons_of_mem _ member))⟩

/-- Startup retains every original operand position, including repetitions. -/
theorem start_supported (nodes : List Node) : Supported nodes (SourceCurrentConjunctionTuplePull.start nodes) := by
  cases nodes with
  | nil => trivial
  | cons first rest =>
      exact fold_supported (first :: rest) rest (.seed first) List.mem_cons_self
        (fun node member => List.mem_cons_of_mem _ member)

/-- A demanded read uses an actual original operand. -/
theorem requested_mem (support : List Node) (cursor : Cursor Symbol Formula) (node : Node)
    (supported : Supported support cursor) (actual : requested cursor = some node) : node ∈ support := by
  induction cursor with
  | empty | seedRows => cases actual
  | seed value => cases actual; exact supported
  | extend value inner ih => exact ih supported.2 actual
  | readOperand value inner tuple _ =>
      cases tuple with
      | nil => cases actual
      | cons first rest => cases actual; exact supported.1
  | scanOperand => cases actual

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

omit [DecidableEq Symbol] in
private theorem expose_native (h : Nat) (node : Node) (before after : Physical Symbol Formula) (rows : List Edge)
    (actual : SourceCurrentConjunctionTuplePull.expose h node before = .done rows after) :
    ∃ edges, MergedFreshOrdinaryExposure.nodeEdges h node before.heap = .done edges after.heap := by
  cases read : MergedFreshOrdinaryExposure.nodeEdges h node before.heap with
  | done edges heap =>
      simp only [SourceCurrentConjunctionTuplePull.expose, SourceCurrentConjunctionRowsWorker.exposures,
        read, Outcome.bind, List.headD_cons] at actual
      have same := congrArg (fun state : Physical Symbol Formula => state.heap) (Outcome.done.inj actual).2
      exact ⟨edges, congrArg (MergedSourceExposure.Result.done edges) same⟩
  | pending | unresolved | exhausted =>
      simp only [SourceCurrentConjunctionTuplePull.expose, SourceCurrentConjunctionRowsWorker.exposures,
        read, Outcome.bind] at actual
      cases actual

/-- A completed transition records its single actual read or its unchanged silent state. -/
theorem step_requested (h : Nat) (cursor : Cursor Symbol Formula)
    (before after : Physical Symbol Formula) (event : Event Symbol Formula)
    (actual : SourceCurrentConjunctionTuplePull.step h cursor before = .done event after) :
    match requested cursor with
    | none => after = before
    | some node => ∃ edges,
        MergedFreshOrdinaryExposure.nodeEdges h node before.heap = .done edges after.heap := by
  induction cursor generalizing before after event with
  | empty => cases actual; rfl
  | seed node =>
      cases read : SourceCurrentConjunctionTuplePull.expose h node before with
      | failed fault middle =>
          simp only [SourceCurrentConjunctionTuplePull.step, read, Outcome.bind] at actual
          cases actual
      | done rows middle =>
          have native := expose_native h node before middle rows read
          simp only [SourceCurrentConjunctionTuplePull.step, read, Outcome.bind] at actual
          cases actual
          exact native
  | seedRows rows => cases rows <;> cases actual <;> rfl
  | extend node inner ih =>
      cases read : SourceCurrentConjunctionTuplePull.step h inner before with
      | failed fault middle =>
          simp only [SourceCurrentConjunctionTuplePull.step, read, Outcome.bind] at actual
          cases actual
      | done innerEvent middle =>
          have own := ih before middle innerEvent read
          cases innerEvent <;> simp only [SourceCurrentConjunctionTuplePull.step, read, Outcome.bind] at actual <;>
            cases actual <;> exact own
  | readOperand node inner tuple _ =>
      cases tuple with
      | nil => cases actual; rfl
      | cons first rest =>
          cases read : SourceCurrentConjunctionTuplePull.expose h node before with
          | failed fault middle =>
              simp only [SourceCurrentConjunctionTuplePull.step, read, Outcome.bind] at actual
              cases actual
          | done rows middle =>
              have native := expose_native h node before middle rows read
              simp only [SourceCurrentConjunctionTuplePull.step, read, Outcome.bind] at actual
              cases actual
              exact native
  | scanOperand node inner tuple rows _ =>
      cases tuple with
      | nil => cases actual; rfl
      | cons first rest =>
          cases rows with
          | nil => cases actual; rfl
          | cons edge rows =>
              simp only [SourceCurrentConjunctionTuplePull.step] at actual
              split at actual <;> (try split at actual) <;> cases actual <;> rfl

/-- Completed cursor reads give the exact heap sequence in actual demand order. -/
theorem step_reads (h : Nat) (cursor : Cursor Symbol Formula)
    (before after : Physical Symbol Formula) (event : Event Symbol Formula)
    (actual : SourceCurrentConjunctionTuplePull.step h cursor before = .done event after) :
    ∃ rows, Exposures (requested cursor).toList before.heap rows after.heap := by
  have observed := step_requested h cursor before after event actual
  cases request : requested cursor with
  | none =>
      rw [request] at observed
      subst after
      exact ⟨[], .nil⟩
  | some node =>
      rw [request] at observed
      obtain ⟨rows, done⟩ := observed
      exact ⟨[rows], .cons (.done h done) .nil⟩

end MicroCFTA.SourceCurrentConjunctionTuplePullReads
