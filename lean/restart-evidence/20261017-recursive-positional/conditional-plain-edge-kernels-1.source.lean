import MicroCFTA.SourceCurrentAllocatedPartialHereditaryPlainEdge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.ConditionalPlainEdgeKernels
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialConditionalDomain (Stored)
open SourceCurrentAllocatedPartialConditionalActive (ActiveAbove PlainEdge)
open SourceCurrentAllocatedPartialActiveOrder (edgeRank nodeRank)
open SourceCurrentAllocatedPartialReturnedDomain (Shape)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Two constructed calls retain the exact intervening context and original filtered ancestor bound. -/
theorem serial
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : EdgeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (plain : PlainEdge request.value) (stored : Stored before) (active : ActiveAbove (edgeRank request) before) :
    ∃ first middle second after next firstMemos final,
      ∃ firstCall : EdgeCall budget request before first middle,
        ∃ secondCall : EdgeCall budget request middle second after,
          EdgeCallReads formulas solver firstCall memos firstMemos ∧
          EdgeCallReads formulas solver secondCall firstMemos final ∧
          Checks (edgeCallTrace firstCall) ∧ Checks (edgeCallTrace secondCall) ∧
          Post formulas solver next before after final ∧ Stored after ∧
          ActiveAbove (edgeRank request) after ∧ Shape request.value first ∧ Shape request.value second := by
  obtain ⟨first, middle, _, firstMemos, _stable, firstCall, firstReads, firstChecks, firstPost,
      _firstResident, firstStored, firstShape, _firstLaw⟩ :=
    SourceCurrentAllocatedPartialConditionalPlainEdge.finite formulas solver budget request initial inherited resident plain stored active
  have middleActive := SourceCurrentAllocatedPartialConditionalFrames.edge_call firstCall active
  have middleInherited := inherited.grows firstPost.effects.grows.constraint_growth
  have middleResident := edge_grows _ _ firstPost.effects.keeps.growth request.value resident
  obtain ⟨second, after, next, final, _stable, secondCall, secondReads, secondChecks, secondPost,
      _secondResident, secondStored, secondShape, _secondLaw⟩ :=
    SourceCurrentAllocatedPartialConditionalPlainEdge.finite formulas solver budget request firstPost.context
      middleInherited middleResident plain firstStored middleActive
  exact ⟨first, middle, second, after, next, firstMemos, final, firstCall, secondCall,
    firstReads, secondReads, firstChecks, secondChecks, firstPost.trans secondPost, secondStored,
    SourceCurrentAllocatedPartialConditionalFrames.edge_call secondCall middleActive, firstShape, secondShape⟩

/-- The actual hereditary producer supplies the smaller Region of every returned child. -/
theorem hereditary_children
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : EdgeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (annotated : SourceCurrentHereditaryConstructors.Edge (fun guard => SourceMemoGate.plain guard = true) request.value)
    (closed : MergedColdReaderClosedInputs.ClosedValues request.value.children)
    (stored : Stored before) (active : ActiveAbove (edgeRank request) before) :
    ∃ result after next final, ∃ actual : EdgeCall budget request before result after,
      EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧
      Post formulas solver next before after final ∧ Stored after ∧
      ∀ (combined : SourceEqualityConstraintAllocation.Value) child, child ∈ result.children →
        SourceEqualityPartialPlainRegion.Region child ∧ nodeRank ⟨combined, child⟩ < edgeRank request := by
  have plain := SourceCurrentAllocatedPartialHereditaryPlainEdge.plain_edge before.checked.native.machine.heap
    initial.ready.semantic.ready.semantic.1.normal.facts request.value resident annotated closed
  obtain ⟨result, after, next, final, _stable, actual, reads, checks, post, _resident, kept, shape, _law⟩ :=
    SourceCurrentAllocatedPartialHereditaryPlainEdge.finite formulas solver budget request initial inherited resident
      annotated closed stored active
  refine ⟨result, after, next, final, actual, reads, checks, post, kept, ?_⟩
  intro combined child member
  have lower := SourceCurrentAllocatedPartialActiveOrder.child_lt_edge request.inherited combined result child member
  have height := shape.height
  refine ⟨shape.child_region plain.2 child member, ?_⟩
  simp only [edgeRank] at lower ⊢
  omega

end MicroCFTA.ConditionalPlainEdgeKernels

#print axioms MicroCFTA.ConditionalPlainEdgeKernels.serial
#check @MicroCFTA.ConditionalPlainEdgeKernels.serial
#print axioms MicroCFTA.ConditionalPlainEdgeKernels.hereditary_children
#check @MicroCFTA.ConditionalPlainEdgeKernels.hereditary_children
