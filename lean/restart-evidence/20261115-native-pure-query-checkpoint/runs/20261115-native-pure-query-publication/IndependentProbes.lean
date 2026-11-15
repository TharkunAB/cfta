import MicroCFTA.SourceCurrentAllocatedNativeQueryInduction
import MicroCFTA.SourceCurrentAllocatedNativePureQueryLaw
import MicroCFTA.SourceCurrentAllocatedNativePureQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativeAuxiliaryPureCutoffQueries
import MicroCFTA.SourceCurrentAllocatedNativeQueryGlobalLaws

#check @MicroCFTA.SourceCurrentAllocatedNativeQueryInduction.query_returned_and_raw_results
#print axioms MicroCFTA.SourceCurrentAllocatedNativeQueryInduction.query_returned_and_raw_results
#check @MicroCFTA.SourceCurrentAllocatedNativePureQueryLaw.raw_result
#print axioms MicroCFTA.SourceCurrentAllocatedNativePureQueryLaw.raw_result
#check @MicroCFTA.SourceCurrentAllocatedNativePureQueryLaw.returned_expected
#print axioms MicroCFTA.SourceCurrentAllocatedNativePureQueryLaw.returned_expected
#check @MicroCFTA.SourceCurrentAllocatedNativePureQueryGlobalLaws.query_returned_and_raw_results
#print axioms MicroCFTA.SourceCurrentAllocatedNativePureQueryGlobalLaws.query_returned_and_raw_results
#check @MicroCFTA.SourceCurrentAllocatedNativePureQueryGlobalLaws.initial_node_query_returned_and_raw_results
#print axioms MicroCFTA.SourceCurrentAllocatedNativePureQueryGlobalLaws.initial_node_query_returned_and_raw_results
#check @MicroCFTA.SourceCurrentAllocatedNativePureQueryGlobalLaws.initial_edge_query_returned_and_raw_results
#print axioms MicroCFTA.SourceCurrentAllocatedNativePureQueryGlobalLaws.initial_edge_query_returned_and_raw_results
#check @MicroCFTA.SourceCurrentAllocatedNativeAuxiliaryPureCutoffQueries.current_stored_universe_auxiliary_pure_cutoff_queries
#print axioms MicroCFTA.SourceCurrentAllocatedNativeAuxiliaryPureCutoffQueries.current_stored_universe_auxiliary_pure_cutoff_queries
#check @MicroCFTA.SourceCurrentAllocatedNativeQueryGlobalLaws.query_returned_and_raw_results
#print axioms MicroCFTA.SourceCurrentAllocatedNativeQueryGlobalLaws.query_returned_and_raw_results
#check @MicroCFTA.SourceCurrentAllocatedNativeQueryGlobalLaws.initial_node_query_returned_and_raw_results
#print axioms MicroCFTA.SourceCurrentAllocatedNativeQueryGlobalLaws.initial_node_query_returned_and_raw_results
#check @MicroCFTA.SourceCurrentAllocatedNativeQueryGlobalLaws.initial_edge_query_returned_and_raw_results
#print axioms MicroCFTA.SourceCurrentAllocatedNativeQueryGlobalLaws.initial_edge_query_returned_and_raw_results

namespace MicroCFTA.NativePureCheckpointProbe
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePureQueryLaw (PureResult)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}
set_option autoImplicit false

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (fuel : Nat) (outerRequest : NodeRequest Symbol Guard)
    (plan : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel
      (.code (.node outerRequest .pure)) ⟨initial width machine, operations⟩)
    (request : NodeRequest Symbol Guard) (expected : Value Symbol Guard)
    (selected : compileNode request = .pure expected) :
    Returned (fun old result => old = request → result = expected)
      (execute fuel (.code (.node outerRequest .pure))
        ⟨initial width machine, operations⟩).state.native.nodes := by
  let reached : Checked width := (execute fuel (.code (.node outerRequest .pure))
    ⟨initial width machine, operations⟩).state
  have family := SourceCurrentAllocatedNativePureQueryGlobalLaws.initial_node_query_returned_and_raw_results
    machine valid operations fuel outerRequest plan
  have pureReturned : Returned PureResult reached.native.nodes := by
    intro handle old result stored
    exact (family.1.1 handle old result stored).2
  exact SourceCurrentAllocatedNativePureQueryLaw.returned_expected
    request reached expected selected pureReturned

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (fuel : Nat) (outerRequest : EdgeRequest Symbol Guard)
    (plan : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel
      (.code (.edge outerRequest .pure)) ⟨initial width machine, operations⟩)
    (request : NodeRequest Symbol Guard) (expected : Value Symbol Guard)
    (selected : compileNode request = .pure expected) :
    Returned (fun old result => old = request → result = expected)
      (execute fuel (.code (.edge outerRequest .pure))
        ⟨initial width machine, operations⟩).state.native.nodes := by
  let reached : Checked width := (execute fuel (.code (.edge outerRequest .pure))
    ⟨initial width machine, operations⟩).state
  have family := SourceCurrentAllocatedNativePureQueryGlobalLaws.initial_edge_query_returned_and_raw_results
    machine valid operations fuel outerRequest plan
  have pureReturned : Returned PureResult reached.native.nodes := by
    intro handle old result stored
    exact (family.1.1 handle old result stored).2
  exact SourceCurrentAllocatedNativePureQueryLaw.returned_expected
    request reached expected selected pureReturned

end MicroCFTA.NativePureCheckpointProbe
