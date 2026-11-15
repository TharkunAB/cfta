import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryResult
import MicroCFTA.SourceCurrentAllocatedNativePrefixOperations
import MicroCFTA.SourceCurrentNativeOpenRequestResults
import MicroCFTA.InternedBoundaryAtoms

/-!
# Closed native reset results under the original parent query

The actual original request keeps its prior coupled ready-cell law.
The reset body emits the same operands at the literal empty domain.
Original plans derive the child's resources and operand availability.
The child hypothesis keeps the original parent prefix and smaller budget.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeClosedResetProfile
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid

set_option autoImplicit false

/-- Closed result syntax retains only the original stored universe boundary atom. -/
def Profile (sourceName : Nat) (value : Value Symbol Guard) : Prop :=
  value.free = [] ∧ ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu sourceName

private theorem through_head
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (fuel : Nat) (control : Control (Value Symbol Guard)) (state : Checked width)
    (plan : InputsThrough fuel control state) : Inputs control state := by
  cases fuel with
  | zero => exact plan
  | succ fuel => exact plan.1

private theorem one_step
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (control next : Control (Value Symbol Guard)) (before after : Checked width)
    (actual : Steps 1 control before next after) :
    SourceEqualityNativeDemand.step control before = .yielded next after := by
  obtain ⟨rest, middle, one, tail⟩ := steps_succ 0 _ _ _ _ actual
  obtain ⟨sameControl, sameState⟩ := steps_zero _ _ _ _ tail
  simpa only [sameControl, sameState] using one

private theorem profile_empty (sourceName : Nat) : Profile sourceName (.empty : Value Symbol Guard) := by
  refine ⟨rfl, ?_⟩
  intro atom member
  simp only [InternedBoundaryAtoms.atoms, List.not_mem_nil] at member

private theorem node_step_returned
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (request : NodeRequest Symbol Guard) (before : Checked width)
    (nodes : Returned nodeLaw before.native.nodes) (edges : Returned edgeLaw before.native.edges) :
    Returned nodeLaw (step (.code (.node request .pure)) before).state.native.nodes ∧
      Returned edgeLaw (step (.code (.node request .pure)) before).state.native.edges := by
  have published : Returned nodeLaw (lookupNode width request before.native).2.nodes ∧
      Returned edgeLaw (lookupNode width request before.native).2.edges := by
    cases keyed : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
    | none => simpa only [lookupNode, keyed] using And.intro nodes edges
    | some physicalKey =>
        constructor
        · simpa only [lookupNode, keyed] using
            SourceCurrentAllocatedNativeContextCache.returned_lookup nodeLaw physicalKey request before.native.nodes nodes
        · simpa only [lookupNode, keyed] using edges
  cases selected : lookupNode width request before.native with
  | mk selection chosen =>
      have chosenNodes : Returned nodeLaw chosen.nodes := by
        simpa only [selected] using published.1
      have chosenEdges : Returned edgeLaw chosen.edges := by
        simpa only [selected] using published.2
      cases selection with
      | direct actual =>
          simpa only [step, SourceRecursiveIntersectionNative.step, selected, lift, Outcome.state] using
            And.intro chosenNodes chosenEdges
      | memoized handle =>
          have demandedNodes : Returned nodeLaw (demandNode handle chosen).2.nodes :=
            SourceCurrentAllocatedNativeContextCache.returned_demand nodeLaw handle chosen.nodes chosenNodes
          have demandedEdges : Returned edgeLaw (demandNode handle chosen).2.edges := chosenEdges
          cases demanded : demandNode handle chosen with
          | mk observation current =>
              have currentNodes : Returned nodeLaw current.nodes := by
                simpa only [demanded] using demandedNodes
              have currentEdges : Returned edgeLaw current.edges := by
                simpa only [demanded] using demandedEdges
              cases observation <;>
                simpa only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift, Outcome.state] using
                  And.intro currentNodes currentEdges

/-- The general closed reset query returns an available profile from the same-prefix smaller empty-domain IH. -/
theorem closed_reset_query_profile_of_fuel_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard) (sourceName : Nat)
    (remainder : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (request : NodeRequest Symbol Guard) (before after : Checked width)
    (parentFuel count : Nat) (value : Value Symbol Guard)
    (physical : Physical before.native) (growth : Grows sourceHeap before.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (plan : InputsThrough parentFuel (.code (.node request .pure)) before)
    (fields : FieldsThrough parentFuel (.code (.node request .pure)) before)
    (nodes : Returned (fun old result => (old = request → Profile sourceName result) ∧ remainder old result)
      before.native.nodes)
    (edges : Returned edgeLaw before.native.edges)
    (leftProfile : Profile sourceName request.left) (rightProfile : Profile sourceName request.right)
    (nonemptyFree : request.domain.key.free.isEmpty = false)
    (bounded : count ≤ parentFuel)
    (actual : Steps count (.code (.node request .pure)) before (.code (.pure value)) after)
    (children : ∀ childFuel, childFuel < parentFuel →
      ∀ childCount, childCount ≤ childFuel →
      ∀ (next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
        (first middle : Checked width) (result : Value Symbol Guard),
      Steps 1 (.code (.node request .pure)) before
        (.code ((requestNode IntersectionEmptyDomain.emptyDomain request.left request.right).bind next)) first →
      Physical first.native → Grows sourceHeap first.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid first.operations →
      InputsThrough childFuel (.code (requestNode IntersectionEmptyDomain.emptyDomain request.left request.right)) first →
      FieldsThrough childFuel (.code (requestNode IntersectionEmptyDomain.emptyDomain request.left request.right)) first →
      Returned (fun old result => (old = request → Profile sourceName result) ∧ remainder old result)
        first.native.nodes → Returned edgeLaw first.native.edges →
      Available first.native.machine.heap request.left → Available first.native.machine.heap request.right →
      Steps childCount (.code (requestNode IntersectionEmptyDomain.emptyDomain request.left request.right)) first
        (.code (.pure result)) middle → Profile sourceName result) :
    Profile sourceName value ∧ Available after.native.machine.heap value ∧ Physical after.native ∧
    Extension before.native.machine after.native.machine ∧ Grows sourceHeap after.native.machine.heap ∧
    SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
    SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations := by
  have current := through_head parentFuel (.code (.node request .pure)) before plan
  have prior : Returned (fun old result => old = request → Profile sourceName result) before.native.nodes := by
    intro handle old result stored
    exact (nodes handle old result stored).1
  have observed : execute (count + 1) (.code (.node request .pure)) before = .done value after :=
    trace_done count _ before after value actual
  have profile : Profile sourceName value := by
    have resultLaw := SourceCurrentAllocatedNativeNodeQueryResult.node_query_result_of_body_induction
      (fun old result => old = request → Profile sourceName result)
      request before after (count + 1) value physical current.1 current.2 prior observed (by
        intro bodySteps bodyBound next first middle result origin bodyTrace
        intro _same
        cases emptyCase : SourceRecursiveIntersectionControl.hasEmpty request.left request.right with
        | true =>
            have selected := SourceRecursiveIntersectionControl.empty_first
              request.domain.key request.left request.right emptyCase
            have compiled : compileNode request = .pure (.empty : Value Symbol Guard) := by
              simp only [compileNode, selected]
            have terminal : Steps bodySteps (.code (.pure (.empty : Value Symbol Guard))) first
                (.code (.pure result)) middle := by
              simpa only [compiled] using bodyTrace
            have same : result = .empty := (pure_trace bodySteps .empty result first middle terminal).2.1.symm
            rw [same]
            exact profile_empty sourceName
        | false =>
            have restart : SourceRecursiveIntersectionControl.reset request.domain.key request.left request.right = true := by
              simp [SourceRecursiveIntersectionControl.reset, leftProfile.1, rightProfile.1, nonemptyFree]
            have selected := SourceRecursiveIntersectionControl.reset_first
              request.domain.key request.left request.right emptyCase restart
            have compiled : compileNode request =
                requestNode IntersectionEmptyDomain.emptyDomain request.left request.right := by
              simp only [compileNode, selected]
            have childOrigin : Steps 1 (.code (.node request .pure)) before
                (.code ((requestNode IntersectionEmptyDomain.emptyDomain request.left request.right).bind next)) first := by
              change Steps 1 (.code (requestNode request.domain request.left request.right)) before
                (.code ((requestNode IntersectionEmptyDomain.emptyDomain request.left request.right).bind next)) first
              simpa only [compiled] using origin
            have childTrace : Steps bodySteps
                (.code (requestNode IntersectionEmptyDomain.emptyDomain request.left request.right)) first
                (.code (.pure result)) middle := by
              simpa only [compiled] using bodyTrace
            have reached := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
              parentFuel 1 (.code (.node request .pure))
              (.code (requestNode IntersectionEmptyDomain.emptyDomain request.left request.right)) next
              before first sourceHeap physical plan fields operationsValid growth childOrigin (by omega)
            obtain ⟨_checked, firstPhysical, _firstExtension, firstGrowth, firstOperations,
              _operationsGrowth, _boundPlan, rawPlan, _boundFields, rawFields⟩ := reached
            have one := one_step (.code (.node request .pure))
              (.code ((compileNode request).bind next)) before first origin
            have firstLaws := node_step_returned
              (fun old result => (old = request → Profile sourceName result) ∧ remainder old result)
              edgeLaw request before nodes edges
            have firstNodes : Returned
                (fun old result => (old = request → Profile sourceName result) ∧ remainder old result)
                first.native.nodes := by
              simpa only [one, Outcome.state] using firstLaws.1
            have firstEdges : Returned edgeLaw first.native.edges := by
              simpa only [one, Outcome.state] using firstLaws.2
            have ready := through_head (parentFuel - 1)
              (.code (requestNode IntersectionEmptyDomain.emptyDomain request.left request.right)) first rawPlan
            exact children (parentFuel - 1) (by omega) bodySteps (by omega) next first middle result
              childOrigin firstPhysical firstGrowth firstOperations rawPlan rawFields firstNodes firstEdges
              ready.1.2.1 ready.1.2.2 childTrace)
    exact resultLaw rfl
  have reached := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    parentFuel count (.code (.node request .pure)) (.code (.pure value)) .pure before after sourceHeap
    physical plan fields operationsValid growth actual bounded
  obtain ⟨checked, afterPhysical, extension, afterGrowth, afterOperations, operationGrowth,
    _boundPlan, _rawPlan, _boundFields, _rawFields⟩ := reached
  have available := SourceCurrentNativeOpenRequestResults.node_result
    count request before after value physical checked
  exact ⟨profile, available, afterPhysical, extension, afterGrowth, afterOperations, operationGrowth⟩

end MicroCFTA.SourceCurrentAllocatedNativeClosedResetProfile

open MicroCFTA.SourceCurrentAllocatedNativeClosedResetProfile
#check closed_reset_query_profile_of_fuel_induction
#print axioms closed_reset_query_profile_of_fuel_induction
