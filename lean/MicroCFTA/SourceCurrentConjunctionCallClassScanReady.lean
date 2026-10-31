import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentConjunctionWorkerWarmEffects

set_option autoImplicit false
open scoped Classical

/-! Probe and readiness preservation at actual conjunction endpoints. -/
namespace MicroCFTA.SourceCurrentConjunctionCallClassScanReady
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual allocated-call outcome retains the complete checked readiness. -/
theorem call_ready {width : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    (p h budget : Nat) (query : Node) (before : Caller width) (memos : EndpointMemoGateTrace.Memos)
    (context : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) (closed : query.free = []) :
    let actual := SourceCurrentAllocatedConjunctionWorker.call p h budget query before.checked before.fourth
    SourceCurrentConjunctionClassScan.Ready actual.state := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked context.ready.good
    context.ready.semantic context.ready.costs
  have produced := SourceCurrentConjunctionWorkerWarmEffects.call_effects p h budget before.fourth query
    (physical before.checked) ready available closed
  have effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked)
      (SourceCurrentConjunctionWorker.call p h budget before.fourth query (physical before.checked)).state := by
    refine Eq.mp ?_ produced
    congr; exact Subsingleton.elim _ _
  cases actual : SourceCurrentConjunctionWorker.call p h budget before.fourth query
      (physical before.checked) with
  | done output after =>
    rcases output with ⟨answer, saved⟩
    simp only [actual, SourceCurrentConjunctionWorker.Outcome.state] at effects
    simpa only [SourceCurrentAllocatedConjunctionWorker.call, actual,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state] using
      SourceCurrentConjunctionClassScan.advance_ready before.checked after context.ready effects
  | failed fault after =>
    simp only [actual, SourceCurrentConjunctionWorker.Outcome.state] at effects
    simpa only [SourceCurrentAllocatedConjunctionWorker.call, actual,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state] using
      SourceCurrentConjunctionClassScan.advance_ready before.checked after context.ready effects

end MicroCFTA.SourceCurrentConjunctionCallClassScanReady
