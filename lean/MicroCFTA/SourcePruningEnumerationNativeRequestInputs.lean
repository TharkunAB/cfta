import MicroCFTA.SourceCurrentAllocatedTargetCallerResources

/-!
# Physical input plans from current caller resources

The caller admission constructs its own completed physical request trace.
That trace supplies every bounded input plan, including shorter prefixes.
No future successful trace is a premise of the public theorem.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeRequestInputs
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open InternedProbeProvenance (Available)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
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
local notation "InputsThrough" => SourceCurrentAllocatedNativePhysicalExecution.InputsThrough
variable {width bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem trace_inputs {steps : Nat} {control : Control Node}
    {before after : Checked width} {value : Node}
    (trace : Trace steps control before (.code (.pure value)) after) :
    ∀ nativeFuel, InputsThrough nativeFuel control before := by
  induction steps generalizing control before with
  | zero =>
      cases trace
      intro nativeFuel
      cases nativeFuel with
      | zero => trivial
      | succ => exact ⟨trivial, trivial⟩
  | succ steps ih =>
      cases trace with
      | cons control before next current final result count currentInputs one tail =>
          intro nativeFuel
          cases nativeFuel with
          | zero => exact currentInputs
          | succ nativeFuel =>
              exact ⟨currentInputs, by
                simpa only [one] using ih tail nativeFuel⟩

/-- Current admission derives every bounded input plan for the literal request. -/
theorem inputs_of_resources (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller (bits + 2)) (left right : Node) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (fits : Fits profile before.checked) (room : Room bits profile)
    (leftAvailable : Available before.checked.native.machine.heap left)
    (rightAvailable : Available before.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nativeFuel : Nat) :
    InputsThrough nativeFuel
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before.checked := by
  obtain ⟨_next, _value, _after, _source, _roots, receipt, _rest⟩ :=
    SourceCurrentAllocatedTargetQuery.finite_caller_resources profile formulas solver inventory
      before left right memos initial fits room leftAvailable rightAvailable leftClosed rightClosed
  cases receipt.actual with
  | run trace => exact trace_inputs trace nativeFuel

end MicroCFTA.SourcePruningEnumerationNativeRequestInputs
