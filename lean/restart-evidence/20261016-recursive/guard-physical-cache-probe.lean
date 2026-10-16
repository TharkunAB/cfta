import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache
open MicroCFTA
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativePhysicalCache
#print axioms SourceCurrentAllocatedNativePhysicalCache.initial_valid
#print axioms SourceCurrentAllocatedNativePhysicalCache.Valid.shape
#print axioms SourceCurrentAllocatedNativePhysicalCache.NodeGood.grows
#print axioms SourceCurrentAllocatedNativePhysicalCache.EdgeGood.grows
#print axioms SourceCurrentAllocatedNativePhysicalCache.advance_valid
#print axioms SourceCurrentAllocatedNativePhysicalCache.lookupNode_valid
#print axioms SourceCurrentAllocatedNativePhysicalCache.lookupEdge_valid
#print axioms SourceCurrentAllocatedNativePhysicalCache.demandNode_valid
#print axioms SourceCurrentAllocatedNativePhysicalCache.demandEdge_valid
#print axioms SourceCurrentAllocatedNativePhysicalCache.finishNode_valid
#print axioms SourceCurrentAllocatedNativePhysicalCache.finishEdge_valid
#print axioms SourceCurrentAllocatedNativePhysicalCache.node_request_exact
#print axioms SourceCurrentAllocatedNativePhysicalCache.edge_request_exact
#print axioms SourceCurrentAllocatedNativePhysicalCache.node_ready_receipt
#print axioms SourceCurrentAllocatedNativePhysicalCache.edge_ready_receipt
#print axioms SourceCurrentAllocatedNativePhysicalCache.node_ready
#print axioms SourceCurrentAllocatedNativePhysicalCache.edge_ready
#print axioms SourceCurrentAllocatedNativePhysicalCache.node_started
#print axioms SourceCurrentAllocatedNativePhysicalCache.edge_started
#print axioms SourceCurrentAllocatedNativePhysicalCache.lookupNode_retains
#print axioms SourceCurrentAllocatedNativePhysicalCache.lookupEdge_retains
#print axioms SourceCurrentAllocatedNativePhysicalCache.demandNode_retains
#print axioms SourceCurrentAllocatedNativePhysicalCache.demandEdge_retains
#print axioms SourceCurrentAllocatedNativePhysicalCache.advance_retains
#print axioms SourceCurrentAllocatedNativePhysicalCache.finishNode_running_other
#print axioms SourceCurrentAllocatedNativePhysicalCache.finishEdge_running_other
#print axioms SourceCurrentAllocatedNativePhysicalCache.of_provenance
#check SourceCurrentAllocatedNativePhysicalCache.Valid
#check SourceCurrentAllocatedNativePhysicalCache.finishNode_valid
#check SourceCurrentAllocatedNativePhysicalCache.finishEdge_valid
#check SourceCurrentAllocatedNativePhysicalCache.node_ready
#check SourceCurrentAllocatedNativePhysicalCache.edge_ready
#check SourceCurrentAllocatedNativePhysicalCache.node_started
#check SourceCurrentAllocatedNativePhysicalCache.edge_started

private def machine : Machine Nat Nat := ⟨InternedConstructorTemplates.empty, Cache.emptyState⟩
private def cold : SourceRecursiveIntersectionThunks.State 8 Nat Nat := initial 8 machine
private def request : NodeRequest Nat Nat := ⟨IntersectionEmptyDomain.emptyDomain, .empty, .empty⟩
private def chosen := (lookupNode 8 request cold).2
private def running := (demandNode 0 chosen).2
private def completed := SourceRecursiveIntersectionThunks.finishNode 0 .empty running
private theorem cold_valid : SourceCurrentAllocatedNativePhysicalCache.Valid cold :=
  SourceCurrentAllocatedNativePhysicalCache.initial_valid machine ⟨InternedNestedFacts.empty_facts, Cache.empty_valid⟩
private theorem request_ready : NodeReady machine request :=
  ⟨empty_domain _, empty_available _, empty_available _⟩
private theorem request_safe : SourceRecursiveIntersectionMemo.KeySafe 8 request.domain request.left request.right := by
  refine ⟨by decide, by decide, .empty, .empty, rfl, rfl, trivial, trivial⟩
private theorem chosen_valid : SourceCurrentAllocatedNativePhysicalCache.Valid chosen :=
  SourceCurrentAllocatedNativePhysicalCache.lookupNode_valid cold cold_valid request request_ready request_safe
private theorem running_valid : SourceCurrentAllocatedNativePhysicalCache.Valid running :=
  SourceCurrentAllocatedNativePhysicalCache.demandNode_valid chosen chosen_valid 0
private theorem completed_valid : SourceCurrentAllocatedNativePhysicalCache.Valid completed :=
  SourceCurrentAllocatedNativePhysicalCache.finishNode_valid running running_valid 0 request .empty (by cbv) (empty_available _)

-- The real typed node table completes and reuses the same physical result.
example : chosen.nodes.cells 0 = some ⟨request, .suspended⟩ := by cbv
example : demandNode 0 chosen = (.evaluate request, running) := by cbv
example : running.nodes.cells 0 = some ⟨request, .evaluating⟩ := by cbv
example : completed.nodes.cells 0 = some ⟨request, .returned .empty⟩ := by cbv
example : lookupNode 8 request completed = (.memoized 0, completed) := by cbv
example : demandNode 0 completed = (.ready .empty, completed) := by cbv
example : completed.nodes.next = 1 ∧ completed.edges.next = 0 := by constructor <;> cbv
example : Available completed.machine.heap (.empty : Value Nat Nat) :=
  (SourceCurrentAllocatedNativePhysicalCache.node_ready request completed completed completed 0 .empty
    completed_valid request_ready request_safe (by cbv) (by cbv)).2.2
example : SourceCurrentAllocatedNativePhysicalCache.Valid (advance completed completed.machine) :=
  SourceCurrentAllocatedNativePhysicalCache.advance_valid completed completed_valid _ completed_valid.machine (.refl _)
example : SourceRecursiveIntersectionThunks.finishNode 0 (.reference (.interned 19)) completed = completed := by cbv

-- The separate real typed edge table has its own handle counter and phase changes.
private def edgeBuilt : EdgeValue Nat Nat × InternedConstructorTemplates.State Nat Nat :=
  run (makeEdge 1 0 []) InternedConstructorTemplates.empty
private def edgeMachine : Machine Nat Nat := ⟨edgeBuilt.2, Cache.emptyState⟩
private def edgeCold : SourceRecursiveIntersectionThunks.State 8 Nat Nat := initial 8 edgeMachine
private def edgeRequest : EdgeRequest Nat Nat := ⟨IntersectionEmptyDomain.emptyDomain, edgeBuilt.1, edgeBuilt.1⟩
private def edgeChosen := (lookupEdge 8 edgeRequest edgeCold).2
private def edgeRunning := (demandEdge 0 edgeChosen).2
private def edgeCompleted := SourceRecursiveIntersectionThunks.finishEdge 0 edgeBuilt.1 edgeRunning
private theorem edge_verified : InternedNestedFacts.Verified
    (InternedConstructorTemplates.empty : InternedConstructorTemplates.State Nat Nat)
    (InternedNestedConstruction.work (makeEdge 1 0 []) InternedConstructorTemplates.empty) EdgeResident :=
  InternedNestedFacts.edge_verified 1 0 [] _ InternedNestedFacts.empty_facts (by intro value member; cases member)
private theorem edge_cold_valid : SourceCurrentAllocatedNativePhysicalCache.Valid edgeCold :=
  SourceCurrentAllocatedNativePhysicalCache.initial_valid edgeMachine ⟨edge_verified.facts, Cache.empty_valid⟩
private theorem edge_resident : EdgeResident edgeMachine.heap edgeBuilt.1 :=
  edge_verified.result _ _ rfl
private theorem edge_ready_input : EdgeReady edgeMachine edgeRequest :=
  ⟨empty_domain _, edge_resident, edge_resident⟩
private theorem edge_safe : SourceRecursiveIntersectionEdgeMemo.KeySafe 8 edgeRequest.domain edgeRequest.left edgeRequest.right := by
  refine ⟨by decide, by decide, by decide, by decide⟩
private theorem edge_chosen_valid : SourceCurrentAllocatedNativePhysicalCache.Valid edgeChosen :=
  SourceCurrentAllocatedNativePhysicalCache.lookupEdge_valid edgeCold edge_cold_valid edgeRequest edge_ready_input edge_safe
private theorem edge_running_valid : SourceCurrentAllocatedNativePhysicalCache.Valid edgeRunning :=
  SourceCurrentAllocatedNativePhysicalCache.demandEdge_valid edgeChosen edge_chosen_valid 0
private theorem edge_completed_valid : SourceCurrentAllocatedNativePhysicalCache.Valid edgeCompleted :=
  SourceCurrentAllocatedNativePhysicalCache.finishEdge_valid edgeRunning edge_running_valid 0 edgeRequest edgeBuilt.1
    (by cbv) edge_resident
example : edgeChosen.edges.cells 0 = some ⟨edgeRequest, .suspended⟩ := by cbv
example : demandEdge 0 edgeChosen = (.evaluate edgeRequest, edgeRunning) := by cbv
example : edgeRunning.edges.cells 0 = some ⟨edgeRequest, .evaluating⟩ := by cbv
example : edgeCompleted.edges.cells 0 = some ⟨edgeRequest, .returned edgeBuilt.1⟩ := by cbv
example : lookupEdge 8 edgeRequest edgeCompleted = (0, edgeCompleted) := by cbv
example : demandEdge 0 edgeCompleted = (.ready edgeBuilt.1, edgeCompleted) := by cbv
example : edgeCompleted.nodes.next = 0 ∧ edgeCompleted.edges.next = 1 := by constructor <;> cbv
example : EdgeResident edgeCompleted.machine.heap edgeBuilt.1 :=
  (SourceCurrentAllocatedNativePhysicalCache.edge_ready edgeRequest edgeCompleted edgeCompleted edgeCompleted 0 edgeBuilt.1
    edge_completed_valid edge_ready_input edge_safe (by cbv) (by cbv)).2.2
example : SourceCurrentAllocatedNativePhysicalCache.Valid edgeCompleted := edge_completed_valid
example : SourceCurrentAllocatedNativePhysicalCache.Valid completed := completed_valid
