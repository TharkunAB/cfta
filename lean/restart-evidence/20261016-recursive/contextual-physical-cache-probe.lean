import MicroCFTA.SourceCurrentAllocatedNativeContextualPhysicalCache
import MicroCFTA.SourceCurrentAllocatedNativeNodeBranches
open MicroCFTA
open Language BinderLanguage Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativeContextCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
#print axioms SourceCurrentAllocatedNativeContextualPhysicalCache.initial_valid
#print axioms SourceCurrentAllocatedNativeContextualPhysicalCache.advance
#print axioms SourceCurrentAllocatedNativeContextualPhysicalCache.lookupNode
#print axioms SourceCurrentAllocatedNativeContextualPhysicalCache.lookupEdge
#print axioms SourceCurrentAllocatedNativeContextualPhysicalCache.demandNode
#print axioms SourceCurrentAllocatedNativeContextualPhysicalCache.demandEdge
#print axioms SourceCurrentAllocatedNativeContextualPhysicalCache.finishNode
#print axioms SourceCurrentAllocatedNativeContextualPhysicalCache.finishEdge
#print axioms SourceCurrentAllocatedNativeContextualPhysicalCache.node_observed_ready
#print axioms SourceCurrentAllocatedNativeContextualPhysicalCache.edge_observed_ready
#print axioms SourceCurrentAllocatedNativeContextualPhysicalCache.node_started
#print axioms SourceCurrentAllocatedNativeContextualPhysicalCache.edge_started
#check SourceCurrentAllocatedNativeContextualPhysicalCache.initial_valid
#check SourceCurrentAllocatedNativeContextualPhysicalCache.advance
#check SourceCurrentAllocatedNativeContextualPhysicalCache.lookupNode
#check SourceCurrentAllocatedNativeContextualPhysicalCache.lookupEdge
#check SourceCurrentAllocatedNativeContextualPhysicalCache.demandNode
#check SourceCurrentAllocatedNativeContextualPhysicalCache.demandEdge
#check SourceCurrentAllocatedNativeContextualPhysicalCache.finishNode
#check SourceCurrentAllocatedNativeContextualPhysicalCache.finishEdge
#check SourceCurrentAllocatedNativeContextualPhysicalCache.node_observed_ready
#check SourceCurrentAllocatedNativeContextualPhysicalCache.edge_observed_ready
#check SourceCurrentAllocatedNativeContextualPhysicalCache.node_started
#check SourceCurrentAllocatedNativeContextualPhysicalCache.edge_started

private def machine : Machine Symbol Guard := ⟨InternedConstructorTemplates.empty, Cache.emptyState⟩
private def cold : SourceRecursiveIntersectionThunks.State 8 Symbol Guard := initial 8 machine
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, .empty, .empty⟩
private def chosen := (lookupNode 8 request cold).2
private def running := (demandNode 0 chosen).2
private def completed := SourceRecursiveIntersectionThunks.finishNode 0 .empty running
private theorem cold_physical : SourceCurrentAllocatedNativePhysicalCache.Valid cold :=
  SourceCurrentAllocatedNativePhysicalCache.initial_valid machine ⟨InternedNestedFacts.empty_facts, Cache.empty_valid⟩
private theorem request_ready : NodeReady machine request :=
  ⟨empty_domain _, empty_available _, empty_available _⟩
private theorem request_safe : SourceRecursiveIntersectionMemo.KeySafe 8 request.domain request.left request.right := by
  refine ⟨by decide, by decide, .empty, .empty, rfl, rfl, trivial, trivial⟩

example : chosen.nodes.cells 0 = some ⟨request, .suspended⟩ := by cbv
example : demandNode 0 chosen = (.evaluate request, running) := by cbv
example : running.nodes.cells 0 = some ⟨request, .evaluating⟩ := by cbv
example : completed.nodes.cells 0 = some ⟨request, .returned .empty⟩ := by cbv
example : lookupNode 8 request completed = (.memoized 0, completed) := by cbv
example : demandNode 0 completed = (.ready .empty, completed) := by cbv
example : completed.nodes.next = 1 ∧ completed.edges.next = 0 := by constructor <;> cbv

-- The literal empty-input law is derived independently, then stored and reused.
example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool) :
    NodeLaw view model ranked holds request .empty ∧
      Contextual view model ranked holds completed ∧
      Available completed.machine.heap (.empty : Value Symbol Guard) := by
  have coldContext := initial_contextual view model ranked holds 8 machine
  have started := SourceCurrentAllocatedNativeContextualPhysicalCache.node_started
    view model ranked holds request request cold chosen running 0 cold_physical coldContext
    request_ready request_safe (by cbv) (by cbv)
  have localLaw := SourceCurrentAllocatedNativeNodeBranches.empty_law
    view model ranked holds request (.inl rfl)
  have finished := SourceCurrentAllocatedNativeContextualPhysicalCache.finishNode
    view model ranked holds running 0 request .empty started.2.1 started.2.2.1
    started.2.2.2 (empty_available _) localLaw
  have ready := SourceCurrentAllocatedNativeContextualPhysicalCache.node_observed_ready
    view model ranked holds request completed completed completed 0 .empty finished.1 finished.2
    request_ready request_safe (by cbv) (by cbv)
  exact ⟨ready.1, ready.2.1, ready.2.2.2⟩
