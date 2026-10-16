import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputExecution
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryBoundedFinite
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProfileBudget

/-!
# Constructed native returns with output profiles and reservations

Initial profiles and constructor headroom construct the actual return.
The same receipt supplies structural, profile, and supply conclusions.
A second query can use the first result with no supplied result profile.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputFinite
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

/-- Initial uniform bounds construct a finite return with its own profile and capacity. -/
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
    (edges : state.native.machine.heap.edges.next + N rows arity bound ≤ 2 ^ (bits + 2)) :
    ∃ fuel value after,
      Receipt fuel (.code (requestNode emptyDomain left right)) state value after
        (fun final value => Available final.heap value) ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ SemanticReady after.native.machine.heap ∧
      Stored after.native ∧ OutputStored after.native ∧ NodeShape (rows * rows) (max arity 1) value ∧
      height value ≤ height left ∧ height value ≤ height right ∧ value.free = [] ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ state.native.machine.heap.nodes.next + N rows arity bound ∧
      after.native.machine.heap.edges.next ≤ state.native.machine.heap.edges.next + N rows arity bound := by
  have leftDomain := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.domain left leftShape
  have rightDomain := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.domain right rightShape
  obtain ⟨fuel, value, after, receipt, afterIdle, afterSemantic, afterStored, domain, firstHeight, secondHeight, free⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryBoundedFinite.of_domain bits holds state good semantic stored idle
      (by omega) (by omega) left right leftAvailable rightAvailable leftDomain rightDomain
  have profile := SourceCurrentAllocatedFiniteOrdinaryOutputExecution.node_trace
    ⟨emptyDomain, left, right⟩ state after fuel value receipt.trace good semantic outputStored rfl rows arity leftShape rightShape
  have literalBound := SourceCurrentAllocatedFiniteOrdinaryProfileBudget.node_budget_le left right leftShape rightShape bound heights
  have supplies := SourceCurrentAllocatedFiniteOrdinaryNativeBudget.node_prefix_budget bits state good left right
    leftAvailable rightAvailable leftDomain rightDomain ⟨by omega, by omega⟩ fuel (.code (.pure value)) after receipt.trace.steps
  exact ⟨fuel, value, after, receipt, afterIdle, afterSemantic, afterStored, profile.1, profile.2,
    firstHeight, secondHeight, free, ⟨by omega, by omega⟩, by omega, by omega⟩

/-- Empty native tables derive both result invariants before the first query. -/
theorem cold (bits rows arity bound : Nat) (holds : Guard → Language.Term Symbol → Bool)
    (state : Checked (bits + 2)) (good : Good state) (semantic : SemanticReady state.native.machine.heap)
    (initial : state.native = SourceRecursiveIntersectionThunks.initial (bits + 2) state.native.machine)
    (left right : Node)
    (leftAvailable : Available state.native.machine.heap left)
    (rightAvailable : Available state.native.machine.heap right)
    (leftShape : NodeShape rows arity left) (rightShape : NodeShape rows arity right)
    (heights : max (height left) (height right) ≤ bound)
    (nodes : state.native.machine.heap.nodes.next + N rows arity bound ≤ 2 ^ bits)
    (edges : state.native.machine.heap.edges.next + N rows arity bound ≤ 2 ^ (bits + 2)) :
    ∃ fuel value after,
      Receipt fuel (.code (requestNode emptyDomain left right)) state value after
        (fun final value => Available final.heap value) ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ SemanticReady after.native.machine.heap ∧
      Stored after.native ∧ OutputStored after.native ∧ NodeShape (rows * rows) (max arity 1) value ∧
      height value ≤ height left ∧ height value ≤ height right ∧ value.free = [] ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ state.native.machine.heap.nodes.next + N rows arity bound ∧
      after.native.machine.heap.edges.next ≤ state.native.machine.heap.edges.next + N rows arity bound := by
  have stored : Stored state.native := by
    rw [initial]
    exact SourceCurrentAllocatedFiniteOrdinaryStored.initial_stored _ _
  have outputStored : OutputStored state.native := by
    rw [initial]
    exact SourceCurrentAllocatedFiniteOrdinaryOutputStored.initial_stored _ _
  have idle : SourceRecursiveIntersectionNative.Idle state.native := by
    rw [initial]
    exact SourceRecursiveIntersectionNative.idle_initial _
  exact finite bits rows arity bound holds state good semantic stored outputStored idle left right
    leftAvailable rightAvailable leftShape rightShape heights nodes edges

/-- Two serial queries use the first produced profile and a reservation computed before either query. -/
theorem serial (bits rows arity bound : Nat) (holds : Guard → Language.Term Symbol → Bool)
    (state : Checked (bits + 2)) (good : Good state) (semantic : SemanticReady state.native.machine.heap)
    (stored : Stored state.native) (outputStored : OutputStored state.native)
    (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (left right : Node)
    (leftAvailable : Available state.native.machine.heap left)
    (rightAvailable : Available state.native.machine.heap right)
    (leftShape : NodeShape rows arity left) (rightShape : NodeShape rows arity right)
    (heights : max (height left) (height right) ≤ bound)
    (nodes : state.native.machine.heap.nodes.next + N rows arity bound + N (rows * rows) (max arity 1) bound ≤ 2 ^ bits)
    (edges : state.native.machine.heap.edges.next + N rows arity bound + N (rows * rows) (max arity 1) bound ≤ 2 ^ (bits + 2)) :
    ∃ firstFuel middle current lastFuel result after,
      Receipt firstFuel (.code (requestNode emptyDomain left right)) state middle current
        (fun final value => Available final.heap value) ∧
      Receipt lastFuel (.code (requestNode emptyDomain middle right)) current result after
        (fun final value => Available final.heap value) ∧
      OutputStored after.native ∧ NodeShape ((rows * rows) * (rows * rows)) (max arity 1) result ∧
      Capacity bits current ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ state.native.machine.heap.nodes.next + N rows arity bound + N (rows * rows) (max arity 1) bound ∧
      after.native.machine.heap.edges.next ≤ state.native.machine.heap.edges.next + N rows arity bound + N (rows * rows) (max arity 1) bound := by
  obtain ⟨firstFuel, middle, current, first, firstIdle, firstSemantic, firstStored, firstOutput,
    firstShape, firstHeight, secondHeight, firstFree, firstCapacity, firstNodes, firstEdges⟩ :=
    finite bits rows arity bound holds state good semantic stored outputStored idle left right
      leftAvailable rightAvailable leftShape rightShape heights (by omega) (by omega)
  have rightShape' : NodeShape (rows * rows) (max arity 1) right :=
    SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.mono right rightShape (Nat.le_mul_self rows) (Nat.le_max_left _ _)
  obtain ⟨lastFuel, result, after, last, lastIdle, lastSemantic, lastStored, lastOutput,
    lastShape, lastFirstHeight, lastSecondHeight, lastFree, lastCapacity, lastNodes, lastEdges⟩ :=
    finite bits (rows * rows) (max arity 1) bound holds current first.good firstSemantic firstStored firstOutput
      firstIdle middle right first.result (first.extension.available right rightAvailable) firstShape rightShape'
      (by omega) (by omega) (by omega)
  exact ⟨firstFuel, middle, current, lastFuel, result, after, first, last, lastOutput,
    by simpa only [Nat.max_assoc, Nat.max_self] using lastShape, firstCapacity, lastCapacity, by omega, by omega⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputFinite
