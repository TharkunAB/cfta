import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardFinite
import MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo
import MicroCFTA.SourceCurrentAllocatedNativeColdClosedExact

namespace MicroCFTA.GuardExecutionIndependentKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Receipt Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryCapacity (Capacity)
open MergedOrdinaryHeight (height edgeHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "GuardStored" => SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored
local notation "GP" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
local notation "GPE" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "stepGuard" => SourceCurrentAllocatedFiniteOrdinaryGuardLimits.step
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "N" => SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget
local notation "E" => SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.edgeBudget
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Cold construction, exact warm repetition, and a new generated-input query share one initial reservation. -/
theorem cold_repeat_generated (bits rows arity bound : Nat) (holds : Guard → Language.Term Symbol → Bool)
    (state : Checked (bits + 2)) (good : Good state) (semantic : SemanticReady state.native.machine.heap)
    (initial : state.native = SourceRecursiveIntersectionThunks.initial (bits + 2) state.native.machine)
    (left right : Node) (leftAvailable : Available state.native.machine.heap left)
    (rightAvailable : Available state.native.machine.heap right)
    (leftShape : NodeShape rows arity left) (rightShape : NodeShape rows arity right)
    (limits : Limits) (leftGuards : GP limits left) (rightGuards : GP limits right)
    (heights : max (height left) (height right) ≤ bound)
    (nodes : state.native.machine.heap.nodes.next + 2 * N rows arity bound + N (rows * rows) (max arity 1) bound ≤ 2 ^ bits)
    (edges : state.native.machine.heap.edges.next + 2 * N rows arity bound + N (rows * rows) (max arity 1) bound ≤ 2 ^ (bits + 2)) :
    ∃ firstFuel first current repeatFuel lastFuel result after,
      Receipt firstFuel (.code (requestNode emptyDomain left right)) state first current
        (fun final value => Available final.heap value) ∧
      Receipt repeatFuel (.code (requestNode emptyDomain left right)) current first current
        (fun final value => Available final.heap value) ∧
      SourceEqualityNativeDemand.execute 2 (.code (requestNode emptyDomain left right)) current = .done first current ∧
      Receipt lastFuel (.code (requestNode emptyDomain first right)) current result after
        (fun final value => Available final.heap value) ∧
      GuardStored after.native ∧ GP (stepGuard (stepGuard limits)) result ∧
      OutputStored after.native ∧ NodeShape ((rows * rows) * (rows * rows)) (max arity 1) result ∧
      Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ state.native.machine.heap.nodes.next + 2 * N rows arity bound + N (rows * rows) (max arity 1) bound ∧
      after.native.machine.heap.edges.next ≤ state.native.machine.heap.edges.next + 2 * N rows arity bound + N (rows * rows) (max arity 1) bound := by
  have stored : Stored state.native := by
    rw [initial]
    exact SourceCurrentAllocatedFiniteOrdinaryStored.initial_stored _ _
  have output : OutputStored state.native := by
    rw [initial]
    exact SourceCurrentAllocatedFiniteOrdinaryOutputStored.initial_stored _ _
  have guardStored : GuardStored state.native := by
    rw [initial]
    exact SourceCurrentAllocatedFiniteOrdinaryGuardStored.initial_stored _ _
  have idle : SourceRecursiveIntersectionNative.Idle state.native := by
    rw [initial]
    exact SourceRecursiveIntersectionNative.idle_initial _
  obtain ⟨firstFuel, first, current, firstReceipt, firstIdle, firstSemantic, firstStored, firstOutput,
    firstShape, firstHeight, _secondHeight, _firstFree, _firstCapacity, firstNodes, firstEdges, firstGuards, firstBound⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryGuardFinite.finite bits rows arity bound holds state good semantic stored output idle
      left right leftAvailable rightAvailable leftShape rightShape heights (by omega) (by omega) guardStored limits leftGuards rightGuards
  have cacheable : ∃ key, SourceRecursiveIntersectionMemo.requestKey (bits + 2) emptyDomain left right = some key := by
    have leftDomain := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.domain left leftShape
    have rightDomain := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.domain right rightShape
    cases leftDomain <;> cases rightDomain <;> exact ⟨_, rfl⟩
  obtain ⟨key, requested⟩ := cacheable
  have warm := SourceCurrentAllocatedNativeCompletedMemo.repeat_of_trace firstFuel ⟨emptyDomain, left, right⟩
    state current first good.native key requested firstReceipt.trace
  obtain ⟨repeatFuel, repeated, repeatState, repeatReceipt, _repeatIdle, _repeatSemantic,
    _repeatStored, _repeatOutput, _repeatShape, _repeatFirstHeight, _repeatSecondHeight,
    _repeatFree, _repeatCapacity, _repeatNodes, _repeatEdges, _repeatGuardStored, _repeatBound⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryGuardFinite.finite bits rows arity bound holds current firstReceipt.good
      firstSemantic firstStored firstOutput firstIdle left right (firstReceipt.extension.available left leftAvailable)
      (firstReceipt.extension.available right rightAvailable) leftShape rightShape heights (by omega) (by omega)
      firstGuards limits leftGuards rightGuards
  obtain ⟨sameValue, sameState⟩ := SourceCurrentAllocatedNativeColdClosedExact.completed_unique (repeatFuel + 1) 2
    (.code (requestNode emptyDomain left right)) current repeatState current repeated first repeatReceipt.done warm.2
  subst repeated
  subst repeatState
  have rightShape' : NodeShape (rows * rows) (max arity 1) right :=
    SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.mono right rightShape (Nat.le_mul_self _) (Nat.le_max_left _ _)
  obtain ⟨lastFuel, result, after, last, _lastIdle, _lastSemantic, _lastStored, lastOutput,
    lastShape, _lastFirstHeight, _lastSecondHeight, _lastFree, lastCapacity, lastNodes, lastEdges, lastGuards, lastBound⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryGuardFinite.finite bits (rows * rows) (max arity 1) bound holds current
      firstReceipt.good firstSemantic firstStored firstOutput firstIdle first right firstReceipt.result
      (firstReceipt.extension.available right rightAvailable) firstShape rightShape' (by omega) (by omega) (by omega)
      firstGuards (stepGuard limits) firstBound
      (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node.mono right rightGuards
        (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.step_ge limits))
  exact ⟨firstFuel, first, current, repeatFuel, lastFuel, result, after, firstReceipt, repeatReceipt, warm.2,
    last, lastGuards, lastBound, lastOutput, by simpa only [Nat.max_assoc, Nat.max_self] using lastShape, lastCapacity, by omega, by omega⟩

/-- A literal warm hit has a one-step physical trace and retains its output certificate at the same full state. -/
theorem warm_node_trace {width : Nat} (request : NodeRequest Symbol Guard) (state : Checked width)
    (handle : Nat) (result : Node) (good : Good state) (semantic : SemanticReady state.native.machine.heap)
    (stored : GuardStored state.native) (ready : NodeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request state.native = (.memoized handle, state.native))
    (demanded : demandNode handle state.native = (.ready result, state.native))
    (seen : request.domain.key.seen = []) (limits : Limits)
    (left : GP limits request.left) (right : GP limits request.right) :
    Trace 1 (.code (requestNode request.domain request.left request.right)) state (.code (.pure result)) state ∧
      SourceEqualityNativeDemand.execute 2 (.code (requestNode request.domain request.left request.right)) state = .done result state ∧
      GuardStored state.native ∧ GP (stepGuard limits) result := by
  have one : SourceEqualityNativeDemand.step (.code (requestNode request.domain request.left request.right)) state =
      .yielded (.code (.pure result)) state := by
    simp only [requestNode, SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded,
      SourceEqualityNativeDemand.lift]
  have trace : Trace 1 (.code (requestNode request.domain request.left request.right)) state (.code (.pure result)) state :=
    .cons _ _ _ _ _ _ 0 ⟨ready, fun _ _ => safe⟩ one (.refl _ _)
  have checked := SourceCurrentAllocatedFiniteOrdinaryGuardExecution.node_trace request state state 1 result
    trace good semantic stored seen limits left right
  exact ⟨trace, SourceEqualityNativeDemand.trace_done 1 _ state state result trace.steps, checked⟩

/-- Actual edge return profiles and constructor counts use the same original uniform input bound. -/
theorem edge_trace_budget (bits rows arity bound : Nat) (left right result : Edge)
    (before after : Checked (bits + 2)) (fuel : Nat)
    (trace : Trace fuel (.code (requestEdge emptyDomain left right)) before (.code (.pure result)) after)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap) (stored : GuardStored before.native)
    (leftResident : EdgeResident before.native.machine.heap left) (rightResident : EdgeResident before.native.machine.heap right)
    (leftShape : EdgeShape rows arity left) (rightShape : EdgeShape rows arity right)
    (limits : Limits) (leftGuards : GPE limits left) (rightGuards : GPE limits right)
    (heights : max (edgeHeight left) (edgeHeight right) ≤ bound) (capacity : Capacity bits before) :
    GuardStored after.native ∧ GPE (stepGuard limits) result ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + E rows arity bound ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + E rows arity bound := by
  have checked := SourceCurrentAllocatedFiniteOrdinaryGuardExecution.edge_trace ⟨emptyDomain, left, right⟩ before after
    fuel result trace good semantic stored rfl limits leftGuards rightGuards
  have costs := SourceCurrentAllocatedFiniteOrdinaryNativeBudget.edge_prefix_budget bits before good left right
    leftResident rightResident (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.domain _ leftShape)
    (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.domain _ rightShape) capacity fuel (.code (.pure result)) after trace.steps
  have uniform := SourceCurrentAllocatedFiniteOrdinaryProfileBudget.edge_budget_le left right leftShape rightShape bound heights
  exact ⟨checked.1, checked.2, by omega, by omega⟩

end MicroCFTA.GuardExecutionIndependentKernels

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 10000000

#check @MicroCFTA.GuardExecutionIndependentKernels.cold_repeat_generated
#print axioms MicroCFTA.GuardExecutionIndependentKernels.cold_repeat_generated

#check @MicroCFTA.GuardExecutionIndependentKernels.warm_node_trace
#print axioms MicroCFTA.GuardExecutionIndependentKernels.warm_node_trace

#check @MicroCFTA.GuardExecutionIndependentKernels.edge_trace_budget
#print axioms MicroCFTA.GuardExecutionIndependentKernels.edge_trace_budget
