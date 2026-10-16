import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputFinite
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardExecution

/-!
# Constructed native queries retain hereditary guard profiles

The existing finite constructor supplies the actual complete receipt.
The guard interpreter follows that same physical trace. All earlier
shape, height, residency, supply, idle, and capacity facts remain present.
No future request, completed body, or result guard law is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardFinite
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Receipt)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
open SourceCurrentAllocatedFiniteOrdinaryCapacity (Capacity)
open MergedOrdinaryHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "N" => SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial shape, guard, and headroom bounds construct the same complete query and all prior facts. -/
theorem finite (bits rows arity bound : Nat) (holds : Guard → Language.Term Symbol → Bool)
    (state : Checked (bits + 2)) (good : Good state) (semantic : SemanticReady state.native.machine.heap)
    (stored : Stored state.native) (outputStored : OutputStored state.native)
    (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (left right : Node)
    (leftAvailable : Available state.native.machine.heap left)
    (rightAvailable : Available state.native.machine.heap right)
    (leftShape : NodeShape rows arity left) (rightShape : NodeShape rows arity right)
    (heights : max (height left) (height right) ≤ bound)
    (nodes : state.native.machine.heap.nodes.next + N rows arity bound ≤ 2 ^ bits)
    (edges : state.native.machine.heap.edges.next + N rows arity bound ≤ 2 ^ (bits + 2))
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored state.native)
    (limits : SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits)
    (leftGuards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node limits left)
    (rightGuards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node limits right) :
    ∃ fuel value after,
      Receipt fuel (.code (requestNode emptyDomain left right)) state value after
        (fun final value => Available final.heap value) ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ SemanticReady after.native.machine.heap ∧
      Stored after.native ∧ OutputStored after.native ∧ NodeShape (rows * rows) (max arity 1) value ∧
      height value ≤ height left ∧ height value ≤ height right ∧ value.free = [] ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ state.native.machine.heap.nodes.next + N rows arity bound ∧
      after.native.machine.heap.edges.next ≤ state.native.machine.heap.edges.next + N rows arity bound ∧
      SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored after.native ∧
      SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
        (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.step limits) value := by
  obtain ⟨fuel, value, after, receipt, afterIdle, afterSemantic, afterStored, afterOutput,
    profile, leftHeight, rightHeight, free, capacity, nodeCount, edgeCount⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOutputFinite.finite bits rows arity bound holds state good semantic
      stored outputStored idle left right leftAvailable rightAvailable leftShape rightShape heights nodes edges
  have guardResult := SourceCurrentAllocatedFiniteOrdinaryGuardExecution.node_trace
    ⟨emptyDomain, left, right⟩ state after fuel value receipt.trace good semantic guards rfl limits leftGuards rightGuards
  exact ⟨fuel, value, after, receipt, afterIdle, afterSemantic, afterStored, afterOutput, profile,
    leftHeight, rightHeight, free, capacity, nodeCount, edgeCount, guardResult.1, guardResult.2⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardFinite
