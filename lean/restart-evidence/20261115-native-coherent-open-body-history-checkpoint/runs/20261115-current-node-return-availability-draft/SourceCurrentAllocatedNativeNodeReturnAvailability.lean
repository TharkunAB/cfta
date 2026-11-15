import MicroCFTA.SourceCurrentNativeOpenRequestResults
import MicroCFTA.SourceCurrentAllocatedNativePrefixInputs

/-!
# Available node results at the original raw endpoint

The original input plan checks the actual bounded query trace.
The existing open-request result law supplies availability at that endpoint.
The same raw count serves both the trace and result law.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeNodeReturnAvailability
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid

set_option autoImplicit false

/-- The original query plan derives availability of the exact raw returned value. -/
theorem node_return_available_from_original_plan
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (fuel count : Nat) (request : NodeRequest Symbol Guard)
    (before after : Checked width) (value : Value Symbol Guard)
    (physical : Physical before.native)
    (plan : InputsThrough fuel (.code (.node request .pure)) before)
    (bounded : count ≤ fuel)
    (actual : Steps count (.code (.node request .pure)) before (.code (.pure value)) after) :
    Available after.native.machine.heap value := by
  have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
    fuel count (.code (.node request .pure)) (.code (.pure value)) .pure
    before after physical plan actual bounded
  exact SourceCurrentNativeOpenRequestResults.node_result count request before after value physical reached.1

end MicroCFTA.SourceCurrentAllocatedNativeNodeReturnAvailability
