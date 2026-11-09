import MicroCFTA.SourceCurrentConjunctionTuplePullEffects
import MicroCFTA.SourceEqualityQueryGlobalMemos

/-!
# Ordered memo receipts for every tuple cursor step

The literal cursor determines each exposure call. Inner cursor reads occur
before outer operand reads. A failed exposure retains its completed memo
calls and exact reached heap. Cursor inspection adds no global call.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullOutcomeMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionRowsWorker (Outcome)
open SourceCurrentConjunctionTuplePull
open SourceCurrentConjunctionTuplePullEffects (Inputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Only the literal cursor branches that expose an operand add exposure calls. -/
def StepReads (h : Nat) : Cursor Symbol FullSyntax.Formula → Physical → Memos → Memos → Prop
  | .empty, _, memos, saved => saved = memos
  | .seed node, before, memos, saved =>
      SourceEqualityQueryGlobalMemos.ExposureReads h node before.heap memos saved
  | .seedRows _, _, memos, saved => saved = memos
  | .extend _ inner, before, memos, saved => StepReads h inner before memos saved
  | .readOperand _ _ [], _, memos, saved => saved = memos
  | .readOperand node _ (_ :: _), before, memos, saved =>
      SourceEqualityQueryGlobalMemos.ExposureReads h node before.heap memos saved
  | .scanOperand _ _ _ _, _, memos, saved => saved = memos

omit [DecidableEq Symbol] in
/-- Actual singleton exposure derives the final bundle on successful and failed outcomes. -/
theorem expose_memos (h : Nat) (node : Node) (before : Physical) (ready : Ready before)
    (available : Available before.heap node) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, SourceEqualityQueryGlobalMemos.ExposureReads h node before.heap memos saved ∧
      Valid (expose h node before).state.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  obtain ⟨saved, reads, coherent, retained⟩ := SourceEqualityQueryGlobalMemos.exposure_memos
    h node before.heap ready.semantic ready.costs available memos valid
  refine ⟨saved, reads, ?_, retained, reads.2⟩
  cases actual : MergedFreshOrdinaryExposure.nodeEdges h node before.heap <;>
    simpa only [expose, SourceCurrentConjunctionRowsWorker.exposures, actual,
      Outcome.bind, Outcome.state, List.headD_cons, MergedSourceExposure.Result.state] using coherent

/-- Every actual cursor step derives its ordered calls and exact returned memo bundle. -/
theorem step_memos (h : Nat) (cursor : Cursor Symbol FullSyntax.Formula) (before : Physical)
    (ready : Ready before) (inputs : Inputs before.heap cursor) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, StepReads h cursor before memos saved ∧ Valid (step h cursor before).state.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  induction cursor generalizing before memos with
  | empty => exact ⟨memos, rfl, valid, extends_refl _, rfl⟩
  | seedRows rows => cases rows <;> exact ⟨memos, rfl, valid, extends_refl _, rfl⟩
  | seed node =>
      obtain ⟨saved, reads, coherent, retained, same⟩ := expose_memos h node before ready inputs memos valid
      refine ⟨saved, reads, ?_, retained, same⟩
      cases actual : expose h node before <;>
        simpa only [step, actual, Outcome.bind, Outcome.state] using coherent
  | extend node inner ih =>
      obtain ⟨saved, reads, coherent, retained, same⟩ := ih before ready inputs.2 memos valid
      refine ⟨saved, reads, ?_, retained, same⟩
      cases actual : step h inner before with
      | failed fault after => simpa only [step, actual, Outcome.bind, Outcome.state] using coherent
      | done event after => cases event <;> simpa only [step, actual, Outcome.bind, Outcome.state] using coherent
  | readOperand node inner tuple =>
      cases tuple with
      | nil => exact ⟨memos, rfl, valid, extends_refl _, rfl⟩
      | cons edge edges =>
          obtain ⟨saved, reads, coherent, retained, same⟩ := expose_memos h node before ready inputs.1 memos valid
          refine ⟨saved, reads, ?_, retained, same⟩
          cases actual : expose h node before <;>
            simpa only [step, actual, Outcome.bind, Outcome.state] using coherent
  | scanOperand node inner tuple rows =>
      cases tuple with
      | nil => exact ⟨memos, rfl, valid, extends_refl _, rfl⟩
      | cons edge edges =>
          cases rows with
          | nil => exact ⟨memos, rfl, valid, extends_refl _, rfl⟩
          | cons row rows =>
              simp only [step]
              split
              · split <;> exact ⟨memos, rfl, valid, extends_refl _, rfl⟩
              · exact ⟨memos, rfl, valid, extends_refl _, rfl⟩

end MicroCFTA.SourceCurrentConjunctionTuplePullOutcomeMemos
