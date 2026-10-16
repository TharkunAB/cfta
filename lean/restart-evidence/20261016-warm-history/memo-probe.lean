import MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo
open MicroCFTA Language Cache InternedBinderProtocol InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
#print axioms SourceCurrentAllocatedNativeCompletedMemo.done_retained
#print axioms SourceCurrentAllocatedNativeCompletedMemo.completed_node
#print axioms SourceCurrentAllocatedNativeCompletedMemo.warm_node
#print axioms SourceCurrentAllocatedNativeCompletedMemo.completed_repeat
#print axioms SourceCurrentAllocatedNativeCompletedMemo.uncacheable_call
#print axioms SourceCurrentAllocatedNativeCompletedMemo.repeat_of_trace
#print axioms SourceCurrentAllocatedNativeCompletedMemo.completed_cases
#check @SourceCurrentAllocatedNativeCompletedMemo.done_retained
#check @SourceCurrentAllocatedNativeCompletedMemo.completed_node
#check @SourceCurrentAllocatedNativeCompletedMemo.warm_node
#check @SourceCurrentAllocatedNativeCompletedMemo.completed_repeat
#check @SourceCurrentAllocatedNativeCompletedMemo.uncacheable_call
#check @SourceCurrentAllocatedNativeCompletedMemo.repeat_of_trace
#check @SourceCurrentAllocatedNativeCompletedMemo.completed_cases

noncomputable section
local instance : DecidableEq Symbol := Classical.typeDecidableEq _
local instance : DecidableEq (EdgeKey Symbol Guard) := Classical.typeDecidableEq _
private def machine : Machine Symbol Guard := ⟨InternedConstructorTemplates.empty, Cache.emptyState⟩
private def cold : SourceEqualityNativeDemand.State 8 := ⟨initial 8 machine, SourceEqualityConstraintMemoAllocation.empty⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, .empty, .empty⟩
private def chosen := (lookupNode 8 request cold.native).2
private def running := (demandNode 0 chosen).2
private def after : SourceEqualityNativeDemand.State 8 :=
  ⟨SourceRecursiveIntersectionThunks.finishNode 0 .empty running, cold.operations⟩
private def key : IntersectionFlatMemoKeyDomain.Triple 8 :=
  IntersectionFlatMemoKeyDomain.flatKey 8 request.domain .empty .empty
private theorem physical : SourceCurrentAllocatedNativePhysicalCache.Valid cold.native :=
  SourceCurrentAllocatedNativePhysicalCache.initial_valid machine ⟨InternedNestedFacts.empty_facts, Cache.empty_valid⟩
private theorem ready : NodeReady cold.native.machine request :=
  ⟨empty_domain _, empty_available _, empty_available _⟩
private theorem safe : SourceRecursiveIntersectionMemo.KeySafe 8 request.domain request.left request.right := by
  refine ⟨by decide, by decide, .empty, .empty, rfl, rfl, trivial, trivial⟩
private theorem requested : SourceRecursiveIntersectionMemo.requestKey 8 request.domain request.left request.right = some key := rfl
private theorem firstDone : SourceEqualityNativeDemand.execute 3 (.code (requestNode request.domain request.left request.right)) cold =
    .done .empty after := by rfl

example : cold.native.nodes.next = 0 ∧ cold.native.edges.next = 0 := by constructor <;> rfl
example : lookupNode 8 request cold.native = (.memoized 0, chosen) := by rfl
example : demandNode 0 chosen = (.evaluate request, running) := by rfl
example : chosen.nodes.cells 0 = some ⟨request, .suspended⟩ := by cbv
example : running.nodes.cells 0 = some ⟨request, .evaluating⟩ := by cbv
example : SourceEqualityNativeDemand.execute 3 (.code (requestNode request.domain request.left request.right)) cold =
    .done .empty after := firstDone
example : after.native.nodes.table key = some 0 := by cbv
example : after.native.nodes.cells 0 = some ⟨request, .returned .empty⟩ := by cbv

-- The completed-observation theorem derives the final cell without being given it.
example : ∃ handle, after.native.nodes.table key = some handle ∧
    after.native.nodes.cells handle = some ⟨request, .returned .empty⟩ :=
  SourceCurrentAllocatedNativeCompletedMemo.completed_node 3 request cold after .empty physical ready safe key requested firstDone

-- The public repeat endpoint consumes only initial checks and the actual cold completion.
example : SourceEqualityNativeDemand.execute 2 (.code (requestNode request.domain request.left request.right)) after = .done .empty after :=
  (SourceCurrentAllocatedNativeCompletedMemo.completed_repeat 3 request cold after .empty physical ready safe key requested firstDone).2
example : after.native.nodes.next = 1 ∧ after.native.edges.next = 0 ∧ after.operations = cold.operations := by
  exact ⟨by cbv, by cbv, rfl⟩
example : SourceEqualityNativeDemand.execute 2 (.code (requestNode request.domain request.left request.right)) after = .done .empty after := by cbv
example : SourceEqualityNativeDemandMemo.Retained cold.native after.native :=
  SourceCurrentAllocatedNativeCompletedMemo.done_retained 3 _ cold after (.empty : Value Symbol Guard) physical.shape firstDone

private def unresolvedRequest : NodeRequest Symbol Guard :=
  ⟨IntersectionEmptyDomain.emptyDomain, .reference (.intersection 0 1), .empty⟩
private theorem unresolved : SourceRecursiveIntersectionMemo.requestKey 8 unresolvedRequest.domain
    unresolvedRequest.left unresolvedRequest.right = none := rfl
private theorem directDone : SourceEqualityNativeDemand.execute 2
    (.code (requestNode unresolvedRequest.domain unresolvedRequest.left unresolvedRequest.right)) cold = .done .empty cold := rfl

-- A placeholder bypasses root publication even though its direct empty body completes.
example : lookupNode 8 unresolvedRequest cold.native = (.direct unresolvedRequest, cold.native) := rfl
example : SourceEqualityNativeDemand.execute 2
    (.code (requestNode unresolvedRequest.domain unresolvedRequest.left unresolvedRequest.right)) cold = .done .empty cold := directDone
example : ∃ count, count + 1 < 2 ∧ Steps count (.code (compileNode unresolvedRequest)) cold (.code (.pure (.empty : Value Symbol Guard))) cold :=
  (SourceCurrentAllocatedNativeCompletedMemo.uncacheable_call 2 unresolvedRequest cold cold .empty unresolved directDone).2
example : SourceRecursiveIntersectionMemo.requestKey 8 unresolvedRequest.domain unresolvedRequest.left unresolvedRequest.right = none ∧
    cold.native.nodes.next = 0 := ⟨unresolved, rfl⟩

private theorem actualTrace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace 2
    (.code (requestNode request.domain request.left request.right)) cold (.code (.pure (.empty : Value Symbol Guard))) after := by
  refine .cons _ _ _ _ _ _ 1 ⟨ready, fun _ _ => safe⟩ rfl ?_
  exact .cons _ _ _ _ _ _ 0 ⟨request, by cbv, empty_available _⟩ rfl (.refl _ _)

-- Reached current physical checks suffice; separate Ready/KeySafe/final checks are derived.
example : (∃ handle, after.native.nodes.table key = some handle ∧
      after.native.nodes.cells handle = some ⟨request, .returned .empty⟩) ∧
    SourceEqualityNativeDemand.execute 2 (.code (requestNode request.domain request.left request.right)) after = .done .empty after :=
  SourceCurrentAllocatedNativeCompletedMemo.repeat_of_trace 2 request cold after .empty physical key requested actualTrace
