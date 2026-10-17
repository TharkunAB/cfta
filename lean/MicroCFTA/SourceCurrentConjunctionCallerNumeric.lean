import MicroCFTA.SourceCurrentConjunctionNumeric
import MicroCFTA.SourceCurrentConstrainedCapOperandFrame
import MicroCFTA.SourceCurrentConstrainedCapRequiredResources
import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentAllocatedProbeConjunction
import MicroCFTA.SourceQueryUnfoldMemo

/-!
# Initial numeric conjunction calls in the full current caller

The initial producer constructs its own conjunction memo call. Its same
return retains the complete query Frame, caller Post, fourth-memo result,
and original numeric forecast. Native cells and outer tables remain exact.
-/
namespace MicroCFTA.SourceCurrentConjunctionCallerNumeric
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
variable {width : Nat}

/-- The initial heap guard carrier and profile determine the returned constructor bounds. -/
noncomputable def forecast (heap : Heap) (budget : Nat) (profile : Profile) : Profile :=
  let resource := SourceCurrentConjunctionWorklistResources.forecast
    (SourceCurrentConjunctionGuardUniverse.guards heap) budget (scalar profile)
  ⟨resource, resource, profile.domains, resource⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- An actual physical call retains the full query Frame at its same returned checked state. -/
theorem of_call (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Checked width} {after : Physical}
    {budget : Nat} {memo saved : Memo} {query : Value Symbol Guard} {answer : Bool}
    (actual : SourceCurrentConjunctionMemo.Call budget memo query (physical before) answer after saved)
    (frame : Frame formulas solver inventory before) (available : Available before.native.machine.heap query)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo) :
    Frame formulas solver inventory (advancePhysical before after) := by
  have effects := SourceCurrentConjunctionClassScan.memo_effects formulas solver actual frame.ready available correct
  have guards := SourceCurrentConjunctionGuard.call Plain actual
    (SourceCurrentAllocatedConjunctionMemo.ready before frame.ready.good frame.ready.semantic frame.ready.costs)
    available frame.context.guards
  exact SourceCurrentConstrainedCapOperandFrame.advance frame effects.1
    (SourceCurrentAllocatedQueryMemo.advance_extension before after effects.2.1) rfl rfl guards

/-- Initial caller invariants construct their own complete numeric conjunction call and full Post. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (query : Value Symbol Guard) (before : Caller width)
    (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Available before.checked.native.machine.heap query) :
    ∃ answer after saved,
      SourceCurrentConjunctionMemo.Call budget before.fourth query (physical before.checked) answer after saved ∧
      Frame formulas solver inventory (advancePhysical before.checked after) ∧
      Post formulas solver inventory before (advance before (advancePhysical before.checked after) saved before.merge) memos ∧
      Fits (forecast before.checked.native.machine.heap budget profile) (advancePhysical before.checked after) ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      (advance before (advancePhysical before.checked after) saved before.merge).nodeResults = before.nodeResults ∧
      (advance before (advancePhysical before.checked after) saved before.merge).edgeResults = before.edgeResults ∧
      (advance before (advancePhysical before.checked after) saved before.merge).merge = before.merge ∧
      (advance before (advancePhysical before.checked after) saved before.merge).fourth = saved ∧
      (∀ work reader, SourceCurrentConjunctionWorklistResources.workerFuel
          (SourceCurrentConjunctionGuardUniverse.guards before.checked.native.machine.heap) budget (scalar profile) ≤ work →
        SourceCurrentConjunctionWorklistResources.readerFuel
          (SourceCurrentConjunctionGuardUniverse.guards before.checked.native.machine.heap) budget (scalar profile) ≤ reader →
        SourceCurrentConjunctionWorker.call work reader budget before.fourth query (physical before.checked) = .done (answer, saved) after) := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good initial.ready.semantic initial.ready.costs
  have scalarFits := (SourceCurrentConstrainedCapRequiredResources.of_checked fits).scalar_fits
  obtain ⟨answer, after, saved, actual, effects, correct, sound, retained, _guards, bounded, done⟩ :=
    SourceCurrentConjunctionNumeric.complete formulas solver budget before.fourth query (physical before.checked)
      (scalar profile) ready available scalarFits initial.correct Plain frame.context.guards
  have returned := of_call formulas solver actual frame available initial.correct
  have probes := SourceCurrentAllocatedProbeConjunction.call_heap actual ready available initial.probes
  have post : Post formulas solver inventory before (advance before (advancePhysical before.checked after) saved before.merge) memos := by
    exact ⟨⟨returned.ready, returned.admitted,
      initial.sound.advance formulas solver _ saved before.merge effects,
      initial.stored.grows effects.keeps, initial.covered, correct,
      SourceQueryUnfoldMemo.valid_grows _ _ initial.ready.semantic effects.keeps memos initial.globals, probes⟩,
      effects, Cache.extends_refl _, retained⟩
  exact ⟨answer, after, saved, actual, returned, post,
    ⟨bounded.nodes, bounded.edges, fits.domains, bounded.stored⟩, sound, rfl, rfl, rfl, rfl, done⟩

end MicroCFTA.SourceCurrentConjunctionCallerNumeric
