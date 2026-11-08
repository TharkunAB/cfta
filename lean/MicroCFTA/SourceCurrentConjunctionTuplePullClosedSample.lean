import MicroCFTA.SourceCurrentConjunctionTuplePullClosed
import MicroCFTA.SourceCurrentConjunctionTuplePullDriveEffects
import MicroCFTA.SourceCurrentConjunctionTuplePullTotal

/-!
# Closed rows in finite and total physical tuple sampling

The actual cursor supplies closed rows. Read effects retain full readiness
at every intermediate state and on failures. Closed row assertions apply
only to successful returned samples. No completed future read is supplied.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullClosedSample
open InternedConstructorTemplates
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionTuplePull (Cursor Event step start)
open SourceCurrentConjunctionTuplePullEffects (Inputs)
open SourceCurrentConjunctionTuplePullClosed (ClosedOperands ClosedRows EventClosed)
open SourceCurrentConjunctionTuplePullDriveEffects (Collected)
open SourceCurrentConjunctionTuplePullAdmission (Status advance drive)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

/-- Each collected tuple contains only closed child values. -/
def ClosedCollected (tuples : List (List Edge)) : Prop :=
  ∀ tuple ∈ tuples, ClosedEdges tuple

/-- Suspended states also retain closed operands and rows in their actual continuation. -/
def StatusClosed : Status Symbol Formula → Prop
  | .running cursor tuples | .overflow tuples cursor =>
      ClosedOperands cursor ∧ ClosedRows cursor ∧ ClosedCollected tuples
  | .fit tuples => ClosedCollected tuples

/-- Total results have the same closed-row meaning as their terminal observations. -/
def ResultClosed : SourceCurrentConjunctionTuplePullTotal.Result Symbol Formula → Prop
  | .fit tuples => ClosedCollected tuples
  | .overflow tuples cursor => ClosedOperands cursor ∧ ClosedRows cursor ∧ ClosedCollected tuples

private def OutcomeClosed : Outcome Symbol Formula (Status Symbol Formula) → Prop
  | .done status _ => StatusClosed status
  | .failed _ _ => True

private theorem append_closed (tuples : List (List Edge)) (tuple : List Edge)
    (prior : ClosedCollected tuples) (own : ClosedEdges tuple) : ClosedCollected (tuples ++ [tuple]) := by
  intro selected member
  rcases List.mem_append.mp member with member | member
  · exact prior selected member
  · simpa only [List.mem_singleton.mp member] using own

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem advance_rows (h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before : Physical Symbol Formula)
    (ready : Ready before) (inputs : Inputs before.heap cursor) (operands : ClosedOperands cursor)
    (rows : ClosedRows cursor) (closed : ClosedCollected collected) :
    OutcomeClosed (advance h budget cursor collected before) := by
  cases actual : step h cursor before with
  | failed fault after => simp only [advance, actual, Outcome.bind, OutcomeClosed]
  | done event after =>
      have first := SourceCurrentConjunctionTuplePullClosed.step_closed h cursor before ready inputs operands rows event after actual
      cases event with
      | ended => simpa only [advance, actual, Outcome.bind, OutcomeClosed, StatusClosed] using closed
      | more next =>
          have continued : StatusClosed (.running next collected) := ⟨first.1, first.2, closed⟩
          simpa only [advance, actual, Outcome.bind, OutcomeClosed] using continued
      | yield tuple next =>
          have sampled := append_closed collected tuple closed first.1
          simp only [advance, actual, Outcome.bind]
          split <;> exact ⟨first.2.1, first.2.2, sampled⟩

private theorem drive_rows (steps h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before : Physical Symbol Formula)
    (ready : Ready before) (inputs : Inputs before.heap cursor) (resident : Collected before.heap collected)
    (operands : ClosedOperands cursor) (rows : ClosedRows cursor) (closed : ClosedCollected collected) :
    OutcomeClosed (drive steps h budget cursor collected before) := by
  induction steps generalizing cursor collected before with
  | zero => exact ⟨operands, rows, closed⟩
  | succ steps ih =>
      have physical := SourceCurrentConjunctionTuplePullDriveEffects.advance_effects h budget cursor collected before ready inputs resident
      have first := advance_rows h budget cursor collected before ready inputs operands rows closed
      cases actual : advance h budget cursor collected before with
      | failed fault after => simp only [drive, actual, Outcome.bind, OutcomeClosed]
      | done status after =>
          have kept : Effects before after := by simpa only [actual, Outcome.state] using physical.1
          have retained := physical.2 status after actual
          rw [actual] at first
          cases status with
          | running next sampled =>
              simpa only [drive, actual, Outcome.bind] using
                ih next sampled after kept.ready retained.1 retained.2 first.1 first.2.1 first.2.2
          | fit sampled => simpa only [drive, actual, Outcome.bind] using first
          | overflow sampled next => simpa only [drive, actual, Outcome.bind] using first

/-- Every finite observation retains all physical effects and every successfully returned closed row. -/
theorem drive_closed (steps h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before : Physical Symbol Formula)
    (ready : Ready before) (inputs : Inputs before.heap cursor) (resident : Collected before.heap collected)
    (operands : ClosedOperands cursor) (rows : ClosedRows cursor) (closed : ClosedCollected collected) :
    Effects before (drive steps h budget cursor collected before).state ∧
      ∀ status after, drive steps h budget cursor collected before = .done status after → StatusClosed status := by
  have physical := SourceCurrentConjunctionTuplePullDriveEffects.drive_effects steps h budget cursor collected before ready inputs resident
  refine ⟨physical.1, ?_⟩
  intro status after actual
  simpa only [actual, OutcomeClosed] using drive_rows steps h budget cursor collected before ready inputs resident operands rows closed

/-- Original closed operands derive all returned-row closure facts for total sampling. -/
theorem sample_closed (h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    Effects before (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before).state ∧
      ∀ result after, SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done result after → ResultClosed result := by
  obtain ⟨steps, observed⟩ := SourceCurrentConjunctionTuplePullTotal.sample_observation h budget nodes before
  have actual := observed 0
  simp only [Nat.add_zero, SourceCurrentConjunctionTuplePullAdmission.sample] at actual
  have first := drive_closed steps h budget (start nodes) [] before ready
    (SourceCurrentConjunctionTuplePullEffects.start_inputs before.heap nodes available)
    (by intro tuple member; cases member)
    (SourceCurrentConjunctionTuplePullClosed.start_closed nodes closed)
    (SourceCurrentConjunctionTuplePullClosed.start_rows nodes)
    (by intro tuple member; cases member)
  have kept := first.1
  rw [actual, SourceCurrentConjunctionTuplePullTotal.observe_state] at kept
  refine ⟨kept, ?_⟩
  intro result after done
  have returned : drive steps h budget (start nodes) [] before = .done result.toStatus after := by
    rw [actual, done]
    rfl
  have rows := first.2 result.toStatus after returned
  cases result <;> exact rows

/-- Every tuple in an actual fitting total sample has closed children. -/
theorem sample_fit (h budget : Nat) (nodes : List Node) (before after : Physical Symbol Formula)
    (tuples : List (List Edge))
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done (.fit tuples) after)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    ∀ tuple ∈ tuples, ClosedEdges tuple :=
  (sample_closed h budget nodes before ready available closed).2 (.fit tuples) after actual

end MicroCFTA.SourceCurrentConjunctionTuplePullClosedSample
