import MicroCFTA.SourcePruningEnumerationTargetQueryProjectable
import MicroCFTA.SourceCurrentAllocatedTargetCallerCreditResources
import MicroCFTA.SourceCurrentAllocatedTargetCallerGuardResources

/-!
# Projectable heaps and caller resources from the same target query

Current numeric admission derives word bounds for the actual native request.
That request constructs one receipt and its physical trace.
The same receipt supplies the full caller postcondition and exact execution.
Its actual step also supplies the original alphabet forecast.
Every finite native observation preserves the current guard support.
-/
namespace MicroCFTA.SourcePruningEnumerationTargetQueryResourcesProjectable
open InternedConstructorTemplates InternedProbeProvenance SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentAllocatedNativeCreditProfile (Admits)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound
local notation "InputsThrough" => SourceCurrentAllocatedNativePhysicalExecution.InputsThrough
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Supported" => Heap
  (fun guard : Guard => ∃ classes, SourceCompactGuards.sourceEqualities guard = some classes)
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Current admission retains one query receipt with its caller, trace, forecast, and guard support. -/
theorem finite
    (alphabet : List Guard) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller (bits + 2)) (left right : Node) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (fits : Fits profile before.checked) (room : Admits bits profile)
    (current : Supported before.checked.native.machine.heap)
    (known : Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (leftAvailable : Available before.checked.native.machine.heap left)
    (rightAvailable : Available before.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    ∃ (next : Inventory) (value : Node) (after : Checked (bits + 2)) (count : Nat),
      next.source = before.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right before.checked value after memos ∧
      Trace count (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
        before.checked (.code (.pure value)) after ∧
      Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before after before.fourth before.merge) memos ∧
      SourceEqualityNativeDemand.execute (instructionBound profile.nodes profile.edges profile.mass + 1)
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before.checked = .done value after ∧
      Heap (fun guard => guard ∈ SourceCurrentGeneratedQueryGuardResources.forecast alphabet profile)
        after.native.machine.heap ∧
      Supported after.native.machine.heap ∧
      (∀ fuel, InputsThrough fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before.checked) ∧
      ∀ (fuel : Nat) (observed : SourceEqualityNativeDemand.Outcome (bits + 2) Node),
        SourceEqualityNativeDemand.execute fuel
          (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before.checked = observed →
        Supported observed.state.native.machine.heap := by
  have ranges := SourceCurrentAllocatedTargetQuery.ready_admitted_ranges profile before.checked
    initial.ready fits room left right leftAvailable rightAvailable leftClosed rightClosed
  obtain ⟨next, value, after, count, source, roots, receipt, trace, supported, plans, observations⟩ :=
    SourcePruningEnumerationTargetQueryProjectable.finite formulas solver inventory left right before.checked
      initial.ready initial.admitted current leftAvailable rightAvailable leftClosed rightClosed ranges memos initial.globals
  have post := SourceCurrentAllocatedTargetQuery.receipt_post initial receipt
  have done := SourceCurrentAllocatedTargetQuery.Step.done_profile profile receipt.actual initial.ready fits
    leftAvailable rightAvailable leftClosed rightClosed
  have carrier := SourceCurrentAllocatedTargetQuery.Step.guard_forecast alphabet profile receipt.actual
    initial.ready fits leftAvailable rightAvailable leftClosed rightClosed known
  exact ⟨next, value, after, count, source, roots, receipt, trace, post, done, carrier,
    supported, plans, observations⟩

end MicroCFTA.SourcePruningEnumerationTargetQueryResourcesProjectable
