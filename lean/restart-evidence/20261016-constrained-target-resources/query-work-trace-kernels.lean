import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryQueryWorkTrace
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudget

namespace MicroCFTA.QueryWorkTraceIndependentKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedFiniteOrdinaryWordExecution (Origins Certified)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (observe nodeRequests edgeRequests)
open SourceCurrentAllocatedFiniteOrdinaryQueryReservations (requestsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- A real makeEdge instruction retains its actual returned constructor heap.
theorem single_makeEdge (bits : Nat) (source : Machine Symbol Guard) (before : Checked (bits + 2))
    (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard)) :
    let job := makeEdge symbol guard children
    let actual := run job before.native.machine.heap
    let after : Checked (bits + 2) :=
      ⟨advance before.native {before.native.machine with heap := actual.2}, before.operations⟩
    step (.code (.work job .pure)) before = .yielded (.code (.pure actual.1)) after ∧
      Trace before.native.machine.heap after.native.machine.heap (observe job before.native.machine.heap) := by
  dsimp only
  refine ⟨rfl, ?_⟩
  exact SourceCurrentAllocatedFiniteOrdinaryQueryWorkTrace.step_trace bits source
    (.code (.work (makeEdge symbol guard children) .pure)) _ before _
    (fun _ => True.intro) rfl

-- The arity-mismatch body updates operations before any constructor Work.
theorem mismatched_body_zero_work (bits : Nat) (source : Machine Symbol Guard)
    (before : Checked (bits + 2)) (request : EdgeRequest Symbol Guard)
    (inputs : SourceCurrentAllocatedFiniteOrdinaryWordCode.EdgeInputs bits source request)
    (mismatch : request.left.children.length ≠ request.right.children.length) :
    let after : Checked (bits + 2) :=
      {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations}
    Trace before.native.machine.heap after.native.machine.heap [] ∧
      step (.edgeBody request .pure) before =
        .yielded (.code ((SourceEqualityNativeCheckedCode.sentinel request.left).bind .pure)) after := by
  dsimp only
  have one : step (.edgeBody request .pure) before =
      .yielded (.code ((SourceEqualityNativeCheckedCode.sentinel request.left).bind .pure))
        {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations} := by
    change SourceEqualityNativeDemand.body request .pure before = _
    unfold SourceEqualityNativeDemand.body
    split
    · rfl
    · contradiction
  exact ⟨SourceCurrentAllocatedFiniteOrdinaryQueryWorkTrace.step_trace bits source
    (.edgeBody request .pure) _ before
    {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations}
    ⟨inputs, fun _ => True.intro⟩ one, one⟩

-- Initial resident domain and capacity give an actual Work trace with an input-only budget.
theorem query_prefix_work_budget (bits : Nat) (before : Checked (bits + 2))
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node left)
    (rightDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node right)
    (capacity : SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits before)
    (fuel : Nat) (next : Control (Value Symbol Guard)) (after : Checked (bits + 2))
    (actual : Steps fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before next after) :
    ∃ requests, Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests + edgeRequests requests ≤
        SourceCurrentAllocatedFiniteOrdinaryNativeBudget.nodeBudget left right := by
  have leftKeys := SourceCurrentAllocatedFiniteOrdinaryKeys.of_available bits before.native.machine.heap
    good.native.machine.1.coherent good.native.machine.1.linked capacity.1 capacity.2 left leftAvailable leftDomain
  have rightKeys := SourceCurrentAllocatedFiniteOrdinaryKeys.of_available bits before.native.machine.heap
    good.native.machine.1.coherent good.native.machine.1.linked capacity.1 capacity.2 right rightAvailable rightDomain
  have certificate := SourceCurrentAllocatedFiniteOrdinaryWordCode.request_node bits before.native.machine
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ ⟨rfl, leftKeys, rightKeys, leftAvailable, rightAvailable⟩
  have origins := Origins.of_valid before.native good.native
  have trace := SourceCurrentAllocatedFiniteOrdinaryQueryWorkTrace.prefix bits before.native.machine
    good.native.machine fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
    next before after origins certificate actual
  have budget := SourceCurrentAllocatedFiniteOrdinaryNativeBudget.node_prefix_budget bits before good
    left right leftAvailable rightAvailable leftDomain rightDomain capacity fuel next after actual
  exact ⟨_, trace, budget.1⟩

-- Two actual prefixes concatenate at the same reached heap and retain exact miss counters.
theorem consecutive_prefixes (bits : Nat) (source : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid source)
    (firstFuel lastFuel : Nat) (control middle next : Control A)
    (before current after : Checked (bits + 2))
    (origins : Origins source before.native) (certificate : Certified bits source control)
    (first : Steps firstFuel control before middle current)
    (last : Steps lastFuel middle current next after) :
    ∃ requests,
      requests = requestsThrough firstFuel control before ++ requestsThrough lastFuel middle current ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next +
        SourceCurrentAllocatedFiniteOrdinaryReservations.nodeReservations requests ∧
      after.native.machine.heap.edges.next = before.native.machine.heap.edges.next +
        SourceCurrentAllocatedFiniteOrdinaryReservations.edgeReservations requests := by
  have reached := SourceCurrentAllocatedFiniteOrdinaryWordExecution.reached bits source valid
    firstFuel control middle before current origins certificate first
  have firstTrace := SourceCurrentAllocatedFiniteOrdinaryQueryWorkTrace.prefix bits source valid
    firstFuel control middle before current origins certificate first
  have lastTrace := SourceCurrentAllocatedFiniteOrdinaryQueryWorkTrace.prefix bits source valid
    lastFuel middle next current after reached.1 reached.2.1 last
  have combined := firstTrace.trans lastTrace
  exact ⟨_, rfl, combined, combined.next_exact⟩

#print axioms single_makeEdge
#check @single_makeEdge
#print axioms mismatched_body_zero_work
#check @mismatched_body_zero_work
#print axioms query_prefix_work_budget
#check @query_prefix_work_budget
#print axioms consecutive_prefixes
#check @consecutive_prefixes
end MicroCFTA.QueryWorkTraceIndependentKernels
