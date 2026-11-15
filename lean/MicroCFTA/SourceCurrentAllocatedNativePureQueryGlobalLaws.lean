import MicroCFTA.SourceCurrentAllocatedNativeQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativePureQueryLaw

/-!
# Exact native shortcut laws from initialized memo history

Literal pure branches retain their exact compiled value.
Closed self requests also retain identity through the reset branch.
The same memo laws hold at every original query endpoint.
Raw results keep the original parent budget.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativePureQueryGlobalLaws
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativeQueryGlobalLaws (SelfResult MismatchResult)
open SourceCurrentAllocatedNativePureQueryLaw (PureResult)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough Inputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
variable {width : Nat}

set_option autoImplicit false

/-- Both exact closed-self and literal pure-result clauses use the same memo cells. -/
def NodeResult [DecidableEq Symbol] (request : NodeRequest Symbol Guard)
    (value : Value Symbol Guard) : Prop :=
  SelfResult request value ∧ PureResult request value

set_option maxHeartbeats 1600000 in
/-- Both memo laws hold at every query endpoint and every bounded raw pure return. -/
theorem query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) :
    (∀ (request : NodeRequest Symbol Guard) (before : Checked width),
      Physical before.native →
      InputsThrough fuel (.code (.node request .pure)) before →
      Returned NodeResult before.native.nodes → Returned MismatchResult before.native.edges →
      (Returned NodeResult (execute fuel (.code (.node request .pure)) before).state.native.nodes ∧
        Returned MismatchResult (execute fuel (.code (.node request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.node request .pure)) before (.code (.pure value)) after →
        NodeResult request value)) ∧
    (∀ (request : EdgeRequest Symbol Guard) (before : Checked width),
      Physical before.native →
      InputsThrough fuel (.code (.edge request .pure)) before →
      Returned NodeResult before.native.nodes → Returned MismatchResult before.native.edges →
      (Returned NodeResult (execute fuel (.code (.edge request .pure)) before).state.native.nodes ∧
        Returned MismatchResult (execute fuel (.code (.edge request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.edge request .pure)) before (.code (.pure value)) after →
        MismatchResult request value)) := by
  refine SourceCurrentAllocatedNativeQueryInduction.query_returned_and_raw_results
    NodeResult MismatchResult ?_ ?_ fuel
  · intro request before first middle parentFuel bodySteps value next
      physical plan entered smaller actual nodeCalls _edgeCalls
    constructor
    · apply SourceCurrentAllocatedNativeRawBodyResults.compile_node_closed_self_trace_result
        request before first middle parentFuel bodySteps value next entered smaller actual
      intro childSteps _small childNext childValue childAfter childEntry childTrace closed
      exact (nodeCalls ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.left⟩
        childNext first childAfter 1 childSteps childValue (by decide) (by omega)
        childEntry childTrace).1 rfl closed
    · exact SourceCurrentAllocatedNativePureQueryLaw.raw_result
        request first middle bodySteps value actual
  · intro request before first middle parentFuel bodySteps value next
      physical plan entered smaller actual _nodeCalls _edgeCalls mismatch
    have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
      parentFuel 1 (.code (.edge request .pure)) (.edgeBody request .pure) next
      before first physical plan entered (by omega)
    exact (SourceCurrentAllocatedNativeRawBodyResults.mismatch_edge_body_trace_result
      request first middle bodySteps value reached.2.1 mismatch actual).1

/-- The actual initial node query starts with both complete memo families empty. -/
theorem initial_node_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (fuel : Nat) (request : NodeRequest Symbol Guard)
    (plan : InputsThrough fuel (.code (.node request .pure)) ⟨initial width machine, operations⟩) :
    (Returned NodeResult (execute fuel (.code (.node request .pure))
      ⟨initial width machine, operations⟩).state.native.nodes ∧
      Returned MismatchResult (execute fuel (.code (.node request .pure))
        ⟨initial width machine, operations⟩).state.native.edges) ∧
    (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
      Steps count (.code (.node request .pure)) ⟨initial width machine, operations⟩ (.code (.pure value)) after →
      NodeResult request value) := by
  exact (query_returned_and_raw_results fuel).1 request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid) plan
    (SourceCurrentAllocatedNativeContextCache.returned_empty NodeResult)
    (SourceCurrentAllocatedNativeContextCache.returned_empty MismatchResult)

/-- The actual initial edge query starts with both complete memo families empty. -/
theorem initial_edge_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (fuel : Nat) (request : EdgeRequest Symbol Guard)
    (plan : InputsThrough fuel (.code (.edge request .pure)) ⟨initial width machine, operations⟩) :
    (Returned NodeResult (execute fuel (.code (.edge request .pure))
      ⟨initial width machine, operations⟩).state.native.nodes ∧
      Returned MismatchResult (execute fuel (.code (.edge request .pure))
        ⟨initial width machine, operations⟩).state.native.edges) ∧
    (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
      Steps count (.code (.edge request .pure)) ⟨initial width machine, operations⟩ (.code (.pure value)) after →
      MismatchResult request value) := by
  exact (query_returned_and_raw_results fuel).2 request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid) plan
    (SourceCurrentAllocatedNativeContextCache.returned_empty NodeResult)
    (SourceCurrentAllocatedNativeContextCache.returned_empty MismatchResult)

end MicroCFTA.SourceCurrentAllocatedNativePureQueryGlobalLaws
