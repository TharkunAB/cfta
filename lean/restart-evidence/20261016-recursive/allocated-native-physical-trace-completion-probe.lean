import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
import MicroCFTA.SourceCurrentAllocatedNativeSemanticHeap
import MicroCFTA.SourceCurrentAllocatedNativeCosts

open MicroCFTA
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges

#print axioms SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace.steps
#print axioms SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace.trans
#print axioms SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace.bind
#print axioms SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace.plan
#print axioms SourceCurrentAllocatedNativePhysicalTraceCompletion.Receipt.done
#print axioms SourceCurrentAllocatedNativePhysicalTraceCompletion.code_complete
#print axioms SourceCurrentAllocatedNativePhysicalTraceCompletion.node_complete
#print axioms SourceCurrentAllocatedNativePhysicalTraceCompletion.edge_complete
#print axioms SourceCurrentAllocatedNativePhysicalTraceCompletion.request_complete
#print axioms SourceCurrentAllocatedNativePhysicalTraceCompletion.initial_complete

#check SourceCurrentAllocatedNativePhysicalTraceCompletion.initial_complete
#check SourceCurrentAllocatedNativePhysicalTraceCompletion.code_complete

/-- One constructed trace gives both the actual return and all reached physical checks. -/
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (before after : Checked width) (value : A) (fuel : Nat)
    (post : Machine Symbol Guard → A → Prop) (receipt : Receipt fuel control before value after post) :
    SourceEqualityNativeDemand.execute (fuel + 1) control before = .done value after ∧
      SourceCurrentAllocatedNativePhysicalExecution.InputsThrough (fuel + 1) control before :=
  ⟨receipt.done, receipt.trace.plan⟩

/-- General closed original roots derive raw actual completion without an own-body done or future input plan. -/
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (state : Checked width) (valid : Good state)
    (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state.native.machine.heap left) (rightAvailable : Available state.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state) :
    ∃ fuel value after,
      SourceEqualityNativeDemand.execute fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state = .done value after ∧
      SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state ∧
      Good after ∧ Extension state.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations after.operations ∧
      Available after.native.machine.heap value ∧ SourceRecursiveIntersectionNative.Idle after.native ∧
      ∀ extra, SourceEqualityNativeDemand.execute (fuel + extra)
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state = .done value after := by
  obtain ⟨fuel, value, after, receipt, afterIdle⟩ :=
    initial_complete holds state valid idle left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  exact ⟨fuel + 1, value, after, receipt.done, receipt.trace.plan, receipt.good, receipt.extension, receipt.keeps,
    receipt.operations, receipt.result, afterIdle, fun extra => done_stable _ extra _ state after value receipt.done⟩

/-- A checked edge body derives its actual return, including the source rejection branch. -/
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (complete : Completes (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request))
    (state : Checked width) (valid : Good state) (ready : EdgeReady state.native.machine request)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : SourceRecursiveIntersectionNative.ActiveAbove (view source holds) holds
      (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete) state.native)
    (ranges : WordRanges (.edgeBody request .pure) state) :
    ∃ fuel value after, SourceEqualityNativeDemand.execute fuel (.edgeBody request .pure) state = .done value after ∧
      Good after ∧ EdgeResident after.native.machine.heap value := by
  obtain ⟨fuel, value, after, receipt⟩ := edge_complete source facts holds request scope complete state valid ready growth history active ranges
  exact ⟨fuel + 1, value, after, receipt.done, receipt.good, receipt.result⟩

/-- Derived physical checks transfer existing initial semantic and cost laws to the same actual returned heap. -/
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (before after : Checked width) (value : A) (fuel : Nat)
    (post : Machine Symbol Guard → A → Prop) (receipt : Receipt fuel control before value after post)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap before.native.machine.heap) :
    SourceEqualityRequiredSemanticCache.SemanticReady after.native.machine.heap ∧
      InternedFreshOrdinaryCostHeap.Heap after.native.machine.heap := by
  have inputs := SourceCurrentAllocatedNativePhysicalExecution.through_heap (fuel + 1) control before receipt.trace.plan
  have keptSemantic := SourceCurrentAllocatedNativeSemanticHeap.execute_semantic (fuel + 1) control before semantic inputs
  have keptCosts := SourceCurrentAllocatedNativeCosts.execute_costs (fuel + 1) control before semantic.ready costs inputs
  exact ⟨by simpa only [receipt.done, Outcome.state] using keptSemantic,
    by simpa only [receipt.done, Outcome.state] using keptCosts⟩
