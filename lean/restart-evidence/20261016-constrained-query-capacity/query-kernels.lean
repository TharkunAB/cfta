import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryQueryReservations
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion

namespace MicroCFTA.QueryReservationIntegration
open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceEqualityNativeDemand
open SourceCurrentAllocatedFiniteOrdinaryReservations
open SourceCurrentAllocatedFiniteOrdinaryQueryReservations
open SourceCurrentAllocatedFiniteOrdinaryWordExecution (Origins Certified)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The literal mismatch prefix changes equality operations before any heap Work request. -/
theorem mismatch_body (before : Checked width) (symbol : Symbol) (guard : Guard) :
    let left : EdgeValue Symbol Guard := .mk ⟨0, ⟨symbol, [], guard⟩⟩ []
    let right : EdgeValue Symbol Guard := .mk ⟨1, ⟨symbol, [.empty], guard⟩⟩ [.empty]
    let request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
    let after := {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations}
    step (.edgeBody request .pure) before =
      .yielded (.code (SourceEqualityNativeCheckedCode.sentinel left)) after ∧
    requestsThrough 1 (.edgeBody request .pure) before = [] ∧
    after.native = before.native := by
  dsimp only
  have one : step (.edgeBody
      ⟨IntersectionEmptyDomain.emptyDomain,
        .mk ⟨0, ⟨symbol, [], guard⟩⟩ [], .mk ⟨1, ⟨symbol, [.empty], guard⟩⟩ [.empty]⟩ .pure) before =
      .yielded (.code (SourceEqualityNativeCheckedCode.sentinel
        (.mk ⟨0, ⟨symbol, [], guard⟩⟩ [])))
        {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations} := by
    simp [step, SourceEqualityNativeDemand.body, sentinel, EdgeValue.children, code_bind_pure]
  exact ⟨one, by simp only [requestsThrough, one]; rfl, rfl⟩

/-- A zero-length raw prefix requires only its initial capacity. -/
theorem zero_prefix (bits : Nat) (before : Checked (bits + 2))
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (capacity : SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits before) :
    SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits before := by
  apply capacity_after bits before.native.machine good.native.machine 0 (.code (.pure ()))
    (.code (.pure ())) before before (Origins.of_valid before.native good.native) trivial (.refl _ _)
  · simpa [requestsThrough, nodeRequests] using capacity.1
  · simpa [requestsThrough, edgeRequests] using capacity.2

/-- A literal edge Work step has one request and the exact initial lookup miss. -/
theorem edge_work_prefix (bits : Nat) (before : Checked (bits + 2))
    (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard)) :
    let job := makeEdge symbol guard children
    let actual := run job before.native.machine.heap
    let after : Checked (bits + 2) :=
      ⟨advance before.native {before.native.machine with heap := actual.2}, before.operations⟩
    Steps 1 (.code (.work job .pure)) before (.code (.pure actual.1)) after ∧
    nodeRequests (requestsThrough 1 (.code (.work job .pure)) before) = 0 ∧
    edgeRequests (requestsThrough 1 (.code (.work job .pure)) before) = 1 ∧
    after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
    after.native.machine.heap.edges.next = before.native.machine.heap.edges.next +
      (if (before.native.machine.heap.edges.table ⟨symbol, children.map Value.referenceOf, guard⟩).isNone then 1 else 0) := by
  dsimp only
  have one : step (.code (.work (makeEdge symbol guard children) .pure)) before =
      .yielded (.code (.pure (run (makeEdge symbol guard children) before.native.machine.heap).1))
        ⟨advance before.native {before.native.machine with heap := (run (makeEdge symbol guard children) before.native.machine.heap).2},
          before.operations⟩ := rfl
  refine ⟨.cons _ _ _ _ _ _ 0 one (.refl _ _), ?_, ?_, ?_⟩
  · simp [requestsThrough, step_requests, one, makeEdge_observe, nodeRequests]
  · simp [requestsThrough, step_requests, one, makeEdge_observe, edgeRequests]
  · have certificate : Certified bits before.native.machine (.code (.work (makeEdge symbol guard children) .pure)) :=
      fun _ => trivial
    have counted := step_counts bits before.native.machine (.code (.work (makeEdge symbol guard children) .pure))
      _ before _ certificate one
    simpa [step_requests, makeEdge_observe, nodeReservations, edgeReservations] using counted

/-- Raw reached prefixes retain original requests and derive their actual supply bounds. -/
theorem raw_prefix (bits : Nat) (source : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid source)
    (fuel : Nat) (control next : Control Output) (before after : Checked (bits + 2))
    (origins : Origins source before.native) (certificate : Certified bits source control)
    (actual : Steps fuel control before next after) :
    Origins source after.native ∧ Certified bits source next ∧
    SourceCurrentAllocatedNativeRequestBounds.Words (bits + 2) next ∧
    after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeRequests (requestsThrough fuel control before) ∧
    after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeRequests (requestsThrough fuel control before) := by
  have reached := SourceCurrentAllocatedFiniteOrdinaryWordExecution.reached bits source valid
    fuel control next before after origins certificate actual
  exact ⟨reached.1, reached.2.1, reached.2.2,
    prefix_bounds bits source valid fuel control next before after origins certificate actual⟩

/-- An actual ready-cell observation skips Work and keeps both heap counters. -/
theorem ready_hit (bits : Nat) (source : Machine Symbol Guard)
    (before : Checked (bits + 2)) (chosen running : SourceRecursiveIntersectionThunks.State (bits + 2) Symbol Guard)
    (request : NodeRequest Symbol Guard) (handle : Nat) (value : Value Symbol Guard)
    (certificate : Certified bits source (.code (requestNode request.domain request.left request.right)))
    (selected : lookupNode (bits + 2) request before.native = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.ready value, running)) :
    let after : Checked (bits + 2) := ⟨running, before.operations⟩
    Steps 1 (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after ∧
    requestsThrough 1 (.code (requestNode request.domain request.left request.right)) before = [] ∧
    after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
    after.native.machine.heap.edges.next = before.native.machine.heap.edges.next := by
  dsimp only
  have one : step (.code (requestNode request.domain request.left request.right)) before =
      .yielded (.code (.pure value)) ⟨running, before.operations⟩ := by
    simp only [requestNode, step, SourceRecursiveIntersectionNative.step, selected, demanded, lift]
  refine ⟨.cons _ _ _ _ _ _ 0 one (.refl _ _), ?_, ?_⟩
  · simp only [requestsThrough, one]; rfl
  · have counted := step_counts bits source _ _ _ _ certificate one
    simpa [step_requests, requestNode, nodeReservations, edgeReservations] using counted

/-- Two actual yielded prefixes compose their request budgets at the same middle state. -/
theorem two_prefix_capacity (bits : Nat) (source : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid source)
    (fuel extra : Nat) (control middle next : Control Output)
    (before current after : Checked (bits + 2))
    (origins : Origins source before.native) (certificate : Certified bits source control)
    (first : Steps fuel control before middle current) (second : Steps extra middle current next after)
    (nodes : before.native.machine.heap.nodes.next + nodeRequests (requestsThrough fuel control before) +
      nodeRequests (requestsThrough extra middle current) ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeRequests (requestsThrough fuel control before) +
      edgeRequests (requestsThrough extra middle current) ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after := by
  have reached := SourceCurrentAllocatedFiniteOrdinaryWordExecution.reached bits source valid
    fuel control middle before current origins certificate first
  have one := prefix_bounds bits source valid fuel control middle before current origins certificate first
  have two := prefix_bounds bits source valid extra middle next current after reached.1 reached.2.1 second
  constructor <;> omega

end MicroCFTA.QueryReservationIntegration

#print axioms MicroCFTA.QueryReservationIntegration.mismatch_body
#check @MicroCFTA.QueryReservationIntegration.mismatch_body
#print axioms MicroCFTA.QueryReservationIntegration.zero_prefix
#check @MicroCFTA.QueryReservationIntegration.zero_prefix
#print axioms MicroCFTA.QueryReservationIntegration.edge_work_prefix
#check @MicroCFTA.QueryReservationIntegration.edge_work_prefix
#print axioms MicroCFTA.QueryReservationIntegration.raw_prefix
#check @MicroCFTA.QueryReservationIntegration.raw_prefix
#print axioms MicroCFTA.QueryReservationIntegration.ready_hit
#check @MicroCFTA.QueryReservationIntegration.ready_hit
#print axioms MicroCFTA.QueryReservationIntegration.two_prefix_capacity
#check @MicroCFTA.QueryReservationIntegration.two_prefix_capacity
