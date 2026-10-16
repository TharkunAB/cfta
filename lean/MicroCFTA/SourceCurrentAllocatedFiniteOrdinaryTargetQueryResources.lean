import MicroCFTA.SourceCurrentAllocatedTargetQuery
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputFinite
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryQueryWorkTrace

/-!
# Initial resources for actual Target intersections

Initial operand profiles and headroom construct the full checked query.
The same actual return supplies its output profile and constructor trace.
No reached range plan, returned profile, or completed query is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetQueryResources
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionCode
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open SourceCurrentAllocatedFiniteOrdinaryQueryReservations (requestsThrough)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open MergedOrdinaryHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "N" => SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Count the exact actual query trace and retain both returned certificate families. -/
theorem counted (bits rows arity bound : Nat) {left right value : Value Symbol Guard}
    {before after : Checked (bits + 2)}
    (actual : SourceCurrentAllocatedTargetQuery.Step left right before value after)
    (ready : Ready before) (stored : Stored before.native) (outputStored : OutputStored before.native)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftShape : NodeShape rows arity left) (rightShape : NodeShape rows arity right)
    (heights : max (height left) (height right) ≤ bound) (capacity : Capacity bits before) :
    Stored after.native ∧ OutputStored after.native ∧ NodeShape (rows * rows) (max arity 1) value ∧
      height value ≤ height left ∧ height value ≤ height right ∧
      ∃ requests, Trace before.native.machine.heap after.native.machine.heap requests ∧
        nodeRequests requests + edgeRequests requests ≤ N rows arity bound ∧
        after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + N rows arity bound ∧
        after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + N rows arity bound := by
  cases actual with
  | @run fuel trace =>
      have leftDomain := NodeShape.domain left leftShape
      have rightDomain := NodeShape.domain right rightShape
      have structural := SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace
        ⟨emptyDomain, left, right⟩ before after fuel value trace ready.good ready.semantic stored
        ⟨rfl, leftDomain, rightDomain⟩
      have output := SourceCurrentAllocatedFiniteOrdinaryOutputExecution.node_trace
        ⟨emptyDomain, left, right⟩ before after fuel value trace ready.good ready.semantic outputStored
        rfl rows arity leftShape rightShape
      have requestsBound := SourceCurrentAllocatedFiniteOrdinaryNativeBudget.node_prefix_budget
        bits before ready.good left right leftAvailable rightAvailable leftDomain rightDomain
        capacity fuel (.code (.pure value)) after trace.steps
      have uniform := SourceCurrentAllocatedFiniteOrdinaryProfileBudget.node_budget_le
        left right leftShape rightShape bound heights
      have leftKeys := SourceCurrentAllocatedFiniteOrdinaryKeys.of_available bits before.native.machine.heap
        ready.good.native.machine.1.coherent ready.good.native.machine.1.linked capacity.1 capacity.2
        left leftAvailable leftDomain
      have rightKeys := SourceCurrentAllocatedFiniteOrdinaryKeys.of_available bits before.native.machine.heap
        ready.good.native.machine.1.coherent ready.good.native.machine.1.linked capacity.1 capacity.2
        right rightAvailable rightDomain
      have certificate : SourceCurrentAllocatedFiniteOrdinaryWordExecution.Certified bits before.native.machine
          (.code (requestNode emptyDomain left right)) :=
        SourceCurrentAllocatedFiniteOrdinaryWordCode.request_node bits before.native.machine
          ⟨emptyDomain, left, right⟩ ⟨rfl, leftKeys, rightKeys, leftAvailable, rightAvailable⟩
      have work := SourceCurrentAllocatedFiniteOrdinaryQueryWorkTrace.prefix bits before.native.machine
        ready.good.native.machine fuel (.code (requestNode emptyDomain left right)) (.code (.pure value)) before after
        (SourceCurrentAllocatedFiniteOrdinaryWordExecution.Origins.of_valid before.native ready.good.native)
        certificate trace.steps
      exact ⟨structural.1, output.1, output.2, structural.2.2.1, structural.2.2.2,
        requestsThrough fuel (.code (requestNode emptyDomain left right)) before, work, by omega, by omega, by omega⟩

/-- Initial profile headroom constructs the full query receipt and its exact resource return. -/
theorem finite (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (bits rows arity bound : Nat) (left right : Value Symbol Guard) (before : Checked (bits + 2))
    (ready : Ready before) (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (stored : Stored before.native) (outputStored : OutputStored before.native)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftShape : NodeShape rows arity left) (rightShape : NodeShape rows arity right)
    (heights : max (height left) (height right) ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + N rows arity bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + N rows arity bound ≤ 2 ^ (bits + 2))
    (memos : EndpointMemoGateTrace.Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ next value after requests,
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right before value after memos ∧
      Stored after.native ∧ OutputStored after.native ∧ NodeShape (rows * rows) (max arity 1) value ∧
      height value ≤ height left ∧ height value ≤ height right ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests + edgeRequests requests ≤ N rows arity bound ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + N rows arity bound ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + N rows arity bound := by
  have initial : Capacity bits before := ⟨by omega, by omega⟩
  have ranges := SourceCurrentAllocatedFiniteOrdinaryWords.node_of_domain bits before ready.good
    initial.1 initial.2 left right leftAvailable rightAvailable
    (NodeShape.domain left leftShape) (NodeShape.domain right rightShape)
  obtain ⟨next, value, after, _source, _roots, receipt⟩ := SourceCurrentAllocatedTargetQuery.finite
    formulas solver inventory left right before ready admitted leftAvailable rightAvailable leftClosed rightClosed ranges memos valid
  obtain ⟨finalStored, finalOutput, profile, firstHeight, secondHeight, requests, work, counted, finalNodes, finalEdges⟩ :=
    counted bits rows arity bound receipt.actual ready stored outputStored leftAvailable rightAvailable
      leftShape rightShape heights initial
  exact ⟨next, value, after, requests, receipt, finalStored, finalOutput, profile, firstHeight, secondHeight,
    work, counted, ⟨by omega, by omega⟩, finalNodes, finalEdges⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetQueryResources
