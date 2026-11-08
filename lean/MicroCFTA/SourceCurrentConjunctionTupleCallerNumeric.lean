import MicroCFTA.SourceCurrentConjunctionDemandWorklistNumeric
import MicroCFTA.SourceCurrentConstrainedCapOperandFrame
import MicroCFTA.SourceCurrentConstrainedCapRequiredResources
import MicroCFTA.SourceCurrentAllocatedTupleConjunctionCaller
import MicroCFTA.SourceCurrentConjunctionDemandGuard

/-!
# Numeric tuple calls in the full current caller

Initial caller facts construct the actual tuple call and its read receipt.
The same return retains the query Frame, full Post, and numeric heap bounds.
The projection and reader ceilings depend on the initial heap and profile.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleCallerNumeric
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapTargetForecast (scalar)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "Call" => SourceCurrentConjunctionDemandWorklistExecution.Call
local notation "CallReads" => SourceCurrentConjunctionDemandWorklistMemos.CallReads
variable {width : Nat}

/-- The original heap guards and profile determine the returned constructor bounds. -/
noncomputable def forecast (heap : Heap) (budget : Nat) (profile : Profile) : Profile :=
  let resource := SourceCurrentConjunctionDemandWorklistNumeric.forecast
    (SourceCurrentConjunctionGuardUniverse.guards heap) budget 1 (scalar profile)
  ⟨resource, resource, profile.domains, resource⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- An actual tuple call preserves the full Frame at its returned checked state. -/
theorem of_call (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Checked width} {after : Physical}
    {budget : Nat} {memo saved : Memo} {query : Value Symbol Guard} {answer : Bool}
    (actual : Call budget memo query (physical before) answer after saved)
    (frame : Frame formulas solver inventory before) (available : Available before.native.machine.heap query)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo) :
    Frame formulas solver inventory (advancePhysical before after) := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before frame.ready.good frame.ready.semantic frame.ready.costs
  have verified := SourceCurrentConjunctionDemandMemo.verified formulas solver actual ready available correct
  have receipt := SourceCurrentAllocatedConjunctionMemo.lift_effects before after frame.ready.good frame.ready.idle verified.1
  have guards := SourceCurrentConjunctionDemandGuard.call Plain actual ready available frame.context.guards
  exact SourceCurrentConstrainedCapOperandFrame.advance frame
    (SourceCurrentConjunctionClassScan.advance_ready before after frame.ready verified.1) receipt.extension rfl rfl guards

/-- Initial caller facts derive the same numeric call, reads, Frame, and full Post. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (query : Value Symbol Guard) (before : Caller width)
    (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Available before.checked.native.machine.heap query) :
    ∃ answer after saved final, ∃ actual : Call budget before.fourth query (physical before.checked) answer after saved,
      CallReads actual memos final ∧
      Frame formulas solver inventory (advancePhysical before.checked after) ∧
      Post formulas solver inventory before (advance before (advancePhysical before.checked after) saved before.merge) final ∧
      Fits (forecast before.checked.native.machine.heap budget profile) (advancePhysical before.checked after) ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧ Available after.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      (advance before (advancePhysical before.checked after) saved before.merge).nodeResults = before.nodeResults ∧
      (advance before (advancePhysical before.checked after) saved before.merge).edgeResults = before.edgeResults ∧
      (advance before (advancePhysical before.checked after) saved before.merge).merge = before.merge ∧
      (advance before (advancePhysical before.checked after) saved before.merge).fourth = saved ∧
      (∀ work reader, SourceCurrentConjunctionDemandWorklistNumeric.workerFuel
          (SourceCurrentConjunctionGuardUniverse.guards before.checked.native.machine.heap) budget 1 (scalar profile) ≤ work →
        SourceCurrentConjunctionDemandWorklistNumeric.readerFuel
          (SourceCurrentConjunctionGuardUniverse.guards before.checked.native.machine.heap) budget 1 (scalar profile) ≤ reader →
        SourceCurrentConjunctionDemandWorker.call work reader budget before.fourth query (physical before.checked) = .done (answer, saved) after) := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good initial.ready.semantic initial.ready.costs
  have scalarFits := (SourceCurrentConstrainedCapRequiredResources.of_checked fits).scalar_fits
  obtain ⟨answer, after, saved, actual, effects, bounded, done⟩ :=
    SourceCurrentConjunctionDemandWorklistNumeric.call_complete budget before.fourth query (physical before.checked)
      (scalar profile) ready available scalarFits
  obtain ⟨final, reads, post, sound, queryAvailable, unfoldings, querySame⟩ :=
    SourceCurrentAllocatedTupleConjunctionCaller.actual formulas solver actual initial available
  have returned := of_call formulas solver actual frame available initial.correct
  exact ⟨answer, after, saved, final, actual, reads, returned, post,
    ⟨bounded.nodes, bounded.edges, fits.domains, bounded.stored⟩, sound, queryAvailable,
    unfoldings, querySame, rfl, rfl, rfl, rfl, done⟩

end MicroCFTA.SourceCurrentConjunctionTupleCallerNumeric
