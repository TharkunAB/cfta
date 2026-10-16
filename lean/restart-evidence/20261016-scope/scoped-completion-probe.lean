import MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion
namespace MicroCFTA.ScopeCompletionProbe
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local notation "ActiveAbove" => SourceRecursiveIntersectionNative.ActiveAbove
local notation "Scoped" => SourceCurrentAllocatedNativeScopeCache.Scoped
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopedCode.certified_bind
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion.Receipt.done
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion.node_complete
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion.edge_complete
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion.request_complete
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion.edge_request_complete
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion.initial_complete
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion.cold_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeScopedCode.certified_bind
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion.Receipt.done
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion.node_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion.edge_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion.request_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion.edge_request_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion.initial_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion.cold_complete

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {A : Type} {width fuel : Nat} {control : Control A} {before after : Checked width} {value : A}
    {post scopePost : Machine Symbol Guard → A → Prop}
    (receipt : SourceCurrentAllocatedNativeScopeCompletion.Receipt fuel control before value after post scopePost) :
    execute (fuel + 1) control before = .done value after ∧ Scoped after.native ∧
    SemanticReady after.native.machine.heap ∧ post after.native.machine value ∧ scopePost after.native.machine value ∧
    SourceCurrentAllocatedNativePhysicalExecution.InputsThrough (fuel + 1) control before :=
  ⟨receipt.done, receipt.scopedCache, receipt.semantic, receipt.result, receipt.law, receipt.trace.plan⟩

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (valid : Good (⟨initial width machine, operations⟩ : Checked width)) (semantic : SemanticReady machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
      (⟨initial width machine, operations⟩ : Checked width)) :
    ∃ fuel value after,
      (∀ extra, execute (fuel + 1 + extra) (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
        (⟨initial width machine, operations⟩ : Checked width) = .done value after) ∧
      Good after ∧ Scoped after.native ∧ SemanticReady after.native.machine.heap ∧
      Available after.native.machine.heap value ∧ SourceRecursiveIntersectionNative.Idle after.native ∧ value.free = [] := by
  obtain ⟨fuel, value, after, receipt, idle, closed⟩ := SourceCurrentAllocatedNativeScopeCompletion.cold_complete
    holds machine operations valid semantic left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  exact ⟨fuel, value, after, (fun extra => done_stable (fuel + 1) extra _ _ _ _ receipt.done),
    receipt.good, receipt.scopedCache, receipt.semantic, receipt.result, idle, closed⟩

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Term Symbol → Bool) (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (complete : Completes (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request))
    (state : Checked width) (valid : Good state) (scopedCache : Scoped state.native)
    (semantic : SemanticReady state.native.machine.heap) (ready : EdgeReady state.native.machine request)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : ActiveAbove (view source holds) holds
      (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete + 1) state.native)
    (ranges : WordRanges (.code (requestEdge request.domain request.left request.right)) state) :
    ∃ fuel value after,
      execute (fuel + 1) (.code (requestEdge request.domain request.left request.right)) state = .done value after ∧
      SourceRecursiveIntersectionResultScope.EdgeScope request.domain.key.seen value ∧
      Scoped after.native ∧ Good after ∧ SemanticReady after.native.machine.heap ∧ EdgeResident after.native.machine.heap value := by
  obtain ⟨fuel, value, after, receipt⟩ := SourceCurrentAllocatedNativeScopeCompletion.edge_request_complete
    source facts holds request scope complete state valid scopedCache semantic ready growth history active ranges
  exact ⟨fuel, value, after, receipt.done, receipt.law, receipt.scopedCache, receipt.good, receipt.semantic, receipt.result⟩

end MicroCFTA.ScopeCompletionProbe
