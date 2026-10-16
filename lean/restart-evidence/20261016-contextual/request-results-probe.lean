import MicroCFTA.SourceCurrentAllocatedNativeRequestResults
open MicroCFTA
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeRequestResults
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

#print axioms finish_node_result
#print axioms finish_edge_result
#print axioms original_key
#print axioms node_result
#print axioms edge_result
#check @finish_node_result
#check @finish_edge_result
#check @original_key
#check @node_result
#check @edge_result

example (request : NodeRequest Symbol Guard) (left : Original request.left) (right : Original request.right) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey 0 request.domain request.left request.right = some key :=
  original_key request left right

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (state : SourceEqualityNativeDemand.State width) (handle : Nat) (request : NodeRequest Symbol Guard)
    (value : Value Symbol Guard) (running : state.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (available : Available state.native.machine.heap value) :
    let after := {state with native := finishNode handle value state.native}
    Trace 1 (.code (.finishNode handle value (.pure value))) state (.code (.pure value)) after ∧
      Available after.native.machine.heap value := by
  let after := {state with native := finishNode handle value state.native}
  have trace : Trace 1 (.code (.finishNode handle value (.pure value))) state (.code (.pure value)) after :=
    .cons _ _ _ _ _ _ 0 ⟨request, running, available⟩ rfl (.refl _ _)
  exact ⟨trace, (finish_node_result 1 handle value value state after trace).2⟩

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (state : SourceEqualityNativeDemand.State width) (handle : Nat) (request : EdgeRequest Symbol Guard)
    (value : EdgeValue Symbol Guard) (running : state.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (resident : EdgeResident state.native.machine.heap value) :
    let after := {state with native := finishEdge handle value state.native}
    Trace 1 (.code (.finishEdge handle value (.pure value))) state (.code (.pure value)) after ∧
      EdgeResident after.native.machine.heap value := by
  let after := {state with native := finishEdge handle value state.native}
  have trace : Trace 1 (.code (.finishEdge handle value (.pure value))) state (.code (.pure value)) after :=
    .cons _ _ _ _ _ _ 0 ⟨request, running, resident⟩ rfl (.refl _ _)
  exact ⟨trace, (finish_edge_result 1 handle value value state after trace).2⟩
