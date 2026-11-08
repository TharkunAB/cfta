import MicroCFTA.SourceCurrentConjunctionTuplePullClosed
import MicroCFTA.SourceCurrentConjunctionTuplePullStability
import MicroCFTA.SourceEqualityProjectionWorkerComplete

/-!
# Successful cursor transitions from current physical inputs

Closed available operands have finite actual row reads. Each cursor step
uses at most one such read. The resulting allowance is stable at every
larger read allowance. No future row list or successful read is an input.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullCompletion
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionTuplePull (Cursor Event expose step)
open SourceCurrentConjunctionTuplePullEffects (Inputs EventInputs)
open SourceCurrentConjunctionTuplePullClosed (ClosedOperands)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

omit [DecidableEq Symbol] in
/-- A current closed operand derives one stable successful physical singleton read. -/
theorem expose_complete (node : Node) (before : Physical Symbol Formula) (ready : Ready before)
    (available : Available before.heap node) (closed : node.free = []) :
    ∃ h rows after, ∀ H, h ≤ H → expose H node before = .done rows after := by
  obtain ⟨rows, heap, actual, _keeps, _semantic, _resident, _closedRows⟩ :=
    SourceEqualityProjectionRead.complete node before.heap ready.semantic available closed
  obtain ⟨h, stable⟩ := SourceEqualityProjectionWorkerComplete.read_stable actual
  refine ⟨h, rows, ⟨heap, before.equality⟩, ?_⟩
  intro H enough
  simp only [expose, SourceCurrentConjunctionRowsWorker.exposures, stable H enough,
    Outcome.bind, List.headD_cons]

private theorem step_done (cursor : Cursor Symbol Formula) :
    ∀ before : Physical Symbol Formula, Ready before → Inputs before.heap cursor → ClosedOperands cursor →
      ∃ h event after, step h cursor before = .done event after := by
  induction cursor with
  | empty => intro before _ready _inputs _closed; exact ⟨0, .ended, before, rfl⟩
  | seed node =>
      intro before ready available closed
      obtain ⟨h, rows, after, stable⟩ := expose_complete node before ready available closed
      exact ⟨h, .more (.seedRows rows), after, by simp only [step, stable h (Nat.le_refl _), Outcome.bind]⟩
  | seedRows rows =>
      intro before _ready _inputs _closed
      cases rows with
      | nil => exact ⟨0, .ended, before, rfl⟩
      | cons edge rows => exact ⟨0, .yield [edge] (.seedRows rows), before, rfl⟩
  | extend node inner ih =>
      intro before ready inputs closed
      obtain ⟨h, event, after, actual⟩ := ih before ready inputs.2 closed.2
      cases event with
      | more next =>
          exact ⟨h, .more (.extend node next), after, by simp only [step, actual, Outcome.bind]⟩
      | yield tuple next =>
          exact ⟨h, .more (.readOperand node next tuple), after, by simp only [step, actual, Outcome.bind]⟩
      | ended => exact ⟨h, .ended, after, by simp only [step, actual, Outcome.bind]⟩
  | readOperand node inner tuple _ih =>
      intro before ready inputs closed
      cases tuple with
      | nil => exact ⟨0, .more (.extend node inner), before, rfl⟩
      | cons first rest =>
          obtain ⟨h, rows, after, stable⟩ := expose_complete node before ready inputs.1 closed.1
          exact ⟨h, .more (.scanOperand node inner (first :: rest) rows), after,
            by simp only [step, stable h (Nat.le_refl _), Outcome.bind]⟩
  | scanOperand node inner tuple remaining _ih =>
      intro before _ready _inputs _closed
      cases tuple with
      | nil => exact ⟨0, .more (.extend node inner), before, rfl⟩
      | cons first rest =>
          cases remaining with
          | nil => exact ⟨0, .more (.extend node inner), before, rfl⟩
          | cons edge rows =>
              let event : Event Symbol Formula :=
                if edge.entry.key.symbol = first.entry.key.symbol then
                  if edge.children.length = first.children.length then
                    .yield (edge :: first :: rest) (.scanOperand node inner (first :: rest) rows)
                  else .more (.scanOperand node inner (first :: rest) rows)
                else .more (.scanOperand node inner (first :: rest) rows)
              refine ⟨0, event, before, ?_⟩
              simp only [step, event]
              split <;> (try split) <;> rfl

/-- Current cursor inputs derive a stable step and its full actual next-state invariants. -/
theorem step_complete (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula)
    (ready : Ready before) (inputs : Inputs before.heap cursor) (closed : ClosedOperands cursor) :
    ∃ h event after,
      (∀ H, h ≤ H → step H cursor before = .done event after) ∧
      Effects before after ∧ EventInputs after.heap event := by
  obtain ⟨h, event, after, actual⟩ := step_done cursor before ready inputs closed
  have effects := SourceCurrentConjunctionTuplePullEffects.step_effects h cursor before ready inputs
  refine ⟨h, event, after, fun _ enough => SourceCurrentConjunctionTuplePullStability.step_done_stable actual enough,
    ?_, effects.2 event after actual⟩
  simpa only [actual, Outcome.state] using effects.1

end MicroCFTA.SourceCurrentConjunctionTuplePullCompletion
