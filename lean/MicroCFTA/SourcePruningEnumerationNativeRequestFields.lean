import MicroCFTA.SourcePruningEnumerationNativeRequestInputs
import MicroCFTA.SourcePruningEnumerationNativeRequestGuardHeap
import MicroCFTA.SourceCurrentAllocatedTargetCallerCreditResources

namespace MicroCFTA.SourcePruningEnumerationNativeRequestFields
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open InternedProbeProvenance (Available)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Current physical checks derive normalized fields at the same supplied budget. -/
theorem fields_through_of_physical_inputs {Output : Type} {width : Nat}
    (fuel : Nat) (control : Control Output) (state : Checked width)
    (valid : SourceCurrentAllocatedNativePhysicalCompletion.Good state)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel control state)
    (fields : SourceCurrentAllocatedNativeFieldClosure.Fields control state) :
    SourceEqualityNativeDemandOperations.FieldsThrough fuel control state := by
  induction fuel generalizing control state with
  | zero =>
      exact SourceCurrentAllocatedNativeFieldClosure.operation_fields control state valid.fields fields
  | succ fuel ih =>
      refine ⟨SourceCurrentAllocatedNativeFieldClosure.operation_fields control state valid.fields fields, ?_⟩
      have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants
        control state valid inputs.1 fields
      cases observed : step control state with
      | yielded next after =>
          have currentGood : SourceCurrentAllocatedNativePhysicalCompletion.Good after := by
            simpa only [observed, Outcome.state] using checked.1
          have currentFields : SourceCurrentAllocatedNativeFieldClosure.Fields next after := by
            simpa only [observed] using checked.2.2.2.2.2
          exact ih next after currentGood
            (by simpa only [SourceCurrentAllocatedNativePhysicalExecution.InputsThrough, observed]
                using inputs.2) currentFields
      | done | failed | constraintError | blocked => trivial

/-- Current caller resources derive the original request field plan. -/
theorem fields_of_resources (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller (bits + 2)) (left right : Node) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (fits : Fits profile before.checked) (room : Room bits profile)
    (leftAvailable : Available before.checked.native.machine.heap left)
    (rightAvailable : Available before.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nativeFuel : Nat) :
    SourceEqualityNativeDemandOperations.FieldsThrough nativeFuel
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before.checked := by
  have inputs := SourcePruningEnumerationNativeRequestInputs.inputs_of_resources
    profile formulas solver inventory before left right memos initial fits room
      leftAvailable rightAvailable leftClosed rightClosed nativeFuel
  exact fields_through_of_physical_inputs nativeFuel _ before.checked initial.ready.good inputs
    (SourcePruningEnumerationNativeRequestGuardHeap.request_allocated before.checked left right)

/-- Either current numeric admission derives both original-budget request plans. -/
theorem admitted_request_plans (profile : Profile) (before : Checked (bits + 2))
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (fits : Fits profile before) (room : SourceCurrentAllocatedNativeCreditProfile.Admits bits profile)
    (left right : Node)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nativeFuel : Nat) :
    SourceCurrentAllocatedNativePhysicalExecution.InputsThrough nativeFuel
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before ∧
      SourceEqualityNativeDemandOperations.FieldsThrough nativeFuel
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before := by
  have ranges := SourceCurrentAllocatedTargetQuery.ready_admitted_ranges
    profile before ready fits room left right leftAvailable rightAvailable leftClosed rightClosed
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left
    before.native.machine.heap ready.good.native.machine.1.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right
    before.native.machine.heap ready.good.native.machine.1.coherent rightAvailable rightClosed
  obtain ⟨_count, _value, _after, receipt, _idle⟩ :=
    SourceCurrentAllocatedNativePhysicalTraceCompletion.initial_complete (fun _ _ => true)
      before ready.good ready.idle left right leftOriginal rightOriginal
      leftAvailable rightAvailable leftClosed rightClosed ranges
  have inputs := SourcePruningEnumerationNativeRequestInputs.completed_trace_inputs receipt.trace nativeFuel
  exact ⟨inputs, fields_through_of_physical_inputs nativeFuel _ before ready.good inputs
    (SourcePruningEnumerationNativeRequestGuardHeap.request_allocated before left right)⟩

end MicroCFTA.SourcePruningEnumerationNativeRequestFields
