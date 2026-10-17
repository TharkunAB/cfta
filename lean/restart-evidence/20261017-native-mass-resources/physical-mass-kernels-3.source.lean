import MicroCFTA.SourceCurrentAllocatedNativePhysicalMass
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.InternedFreshOrdinaryFacts

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.PhysicalMassKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open InternedNestedConstruction (Syntax Outcome)
open SourceCurrentAllocatedNativePhysicalMass
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Stored" => InternedValueMassHeap.Stored
local notation "initialBound" => InternedValueMassHeap.initialBound

private def plan : Syntax Nat Bool :=
  .node [.mk 0 false [.binder false (.node [.mk 1 true [.var 0]]), .node [.mk 2 true []]]]
private def built := InternedFreshOrdinaryConstruction.build plan [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def source := built.state
private def extra := run (makeEdge (99 : Nat) false [root, root]) source
private def heap := extra.2
private def row := extra.1
private def machine : Machine Nat Bool := ⟨heap, Cache.emptyState⟩
private def base : Native 8 Nat Bool := initial 8 machine
private def nodeRequest : NodeRequest Nat Bool := ⟨IntersectionEmptyDomain.emptyDomain, root, root⟩
private def edgeRequest : EdgeRequest Nat Bool := ⟨IntersectionEmptyDomain.emptyDomain, row, row⟩
private def nodePublished := (lookupNode 8 nodeRequest base).2
private def nodeRunning := (demandNode 0 nodePublished).2
private def nodeFinished := finishNode 0 root nodeRunning
private def edgePublished := (lookupEdge 8 edgeRequest nodeFinished).2
private def edgeRunning := (demandEdge 0 edgePublished).2
private def edgeFinished := finishEdge 0 row edgeRunning

private theorem nodePublished_machine : nodePublished.machine = machine :=
  SourceRecursiveIntersectionNative.lookupNode_machine nodeRequest base

private theorem nodeRunning_machine : nodeRunning.machine = machine := nodePublished_machine
private theorem nodeFinished_machine : nodeFinished.machine = machine := nodeRunning_machine
private theorem edgePublished_machine : edgePublished.machine = machine := nodeFinished_machine
private theorem edgeRunning_machine : edgeRunning.machine = machine := edgePublished_machine
private theorem edgeFinished_machine : edgeFinished.machine = machine := edgeRunning_machine

private theorem constructed : built = .done root source := by
  obtain ⟨value, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete plan
  simp only [built, root, source, done, Outcome.state]

private theorem source_facts : Facts source :=
  (InternedFreshOrdinaryFacts.closed_verified plan).facts

private theorem root_available : Available source root :=
  (InternedFreshOrdinaryFacts.closed_verified plan).result root source constructed

private theorem extra_verified : Verified source (InternedNestedConstruction.work (makeEdge (99 : Nat) false [root, root]) source) EdgeResident :=
  InternedNestedFacts.edge_verified (99 : Nat) false [root, root] source source_facts
    (by
      intro value member
      have same : value = root := by simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_self] using member
      subst value
      exact root_available)

private theorem heap_facts : Facts heap := extra_verified.facts
private theorem available : Available heap root := extra_verified.available root root_available
private theorem resident : EdgeResident heap row := extra_verified.result row heap rfl

private theorem base_valid : SourceCurrentAllocatedNativePhysicalCache.Valid base :=
  SourceCurrentAllocatedNativePhysicalCache.initial_valid machine ⟨heap_facts, Cache.empty_valid⟩

private theorem node_ready : NodeReady machine nodeRequest := ⟨empty_domain machine, available, available⟩
private theorem edge_ready : EdgeReady machine edgeRequest := ⟨empty_domain machine, resident, resident⟩

private theorem node_finished_valid : SourceCurrentAllocatedNativePhysicalCache.Valid nodeFinished := by
  have safe : SourceRecursiveIntersectionMemo.KeySafe 8 nodeRequest.domain nodeRequest.left nodeRequest.right := by
    unfold SourceRecursiveIntersectionMemo.KeySafe
    refine ⟨by decide, by decide, .node 5, .node 5, ?_, ?_, ?_, ?_⟩ <;> decide
  have published := SourceCurrentAllocatedNativePhysicalCache.lookupNode_valid base base_valid nodeRequest node_ready safe
  have running := SourceCurrentAllocatedNativePhysicalCache.demandNode_valid nodePublished published 0
  have captured : nodeRunning.nodes.cells 0 = some ⟨nodeRequest, .evaluating⟩ := by cbv
  exact SourceCurrentAllocatedNativePhysicalCache.finishNode_valid nodeRunning running 0 nodeRequest root captured (by simpa only [nodeRunning_machine, machine] using available)

/-- A recursive source publishes a real node cell, finishes it, and observes the same bounded warm payload without effects. -/
theorem constructed_node_warm :
    InternedFreshOrdinaryConstruction.build plan [] empty = .done root source ∧
      nodePublished.nodes.next = 1 ∧
      nodePublished.nodes.cells 0 = some ⟨nodeRequest, .suspended⟩ ∧
      nodeRunning.nodes.cells 0 = some ⟨nodeRequest, .evaluating⟩ ∧
      nodeFinished.nodes.cells 0 = some ⟨nodeRequest, .returned root⟩ ∧
      NodeMass (initialBound heap) ⟨nodeRequest, .suspended⟩ ∧
      NodeMass (initialBound heap) ⟨nodeRequest, .evaluating⟩ ∧
      NodeMass (initialBound heap) ⟨nodeRequest, .returned root⟩ ∧
      lookupNode 8 nodeRequest nodeFinished = (.memoized 0, nodeFinished) ∧
      demandNode 0 nodeFinished = (.ready root, nodeFinished) ∧
      InternedValueMass.value root ≤ initialBound heap ∧
      SourceCurrentAllocatedNativePhysicalCache.Valid nodeFinished := by
  have safe : SourceRecursiveIntersectionMemo.KeySafe 8 nodeRequest.domain nodeRequest.left nodeRequest.right := by
    unfold SourceRecursiveIntersectionMemo.KeySafe
    refine ⟨by decide, by decide, .node 5, .node 5, ?_, ?_, ?_, ?_⟩ <;> decide
  have published := SourceCurrentAllocatedNativePhysicalCache.lookupNode_valid base base_valid nodeRequest node_ready safe
  have running := SourceCurrentAllocatedNativePhysicalCache.demandNode_valid nodePublished published 0
  have first : nodePublished.nodes.cells 0 = some ⟨nodeRequest, .suspended⟩ := by cbv
  have second : nodeRunning.nodes.cells 0 = some ⟨nodeRequest, .evaluating⟩ := by cbv
  have last : nodeFinished.nodes.cells 0 = some ⟨nodeRequest, .returned root⟩ := by cbv
  have stored := InternedValueMassHeap.initial heap heap_facts
  have firstMass := node_cell nodePublished published (by simpa only [nodePublished_machine, machine] using stored) 0 _ first
  have secondMass := node_cell nodeRunning running (by simpa only [nodeRunning_machine, machine] using stored) 0 _ second
  have lastMass := node_cell nodeFinished node_finished_valid (by simpa only [nodeFinished_machine, machine] using stored) 0 _ last
  have initial := initial_cells nodeFinished node_finished_valid
  have supplied : InternedValueMass.value root ≤ initialBound heap := by
    simpa only [nodeFinished_machine, machine] using (initial.1 0 _ last).2.2
  refine ⟨constructed, by cbv, first, second, last, firstMass, secondMass, lastMass,
    ?_, ?_, supplied, node_finished_valid⟩ <;> cbv

/-- The same populated node table survives a real edge publication and warm row demand; complete child width and current readback share its computed mass bound. -/
theorem constructed_edge_warm :
    edgePublished.nodes = nodeFinished.nodes ∧
      edgePublished.edges.next = 1 ∧
      edgePublished.edges.cells 0 = some ⟨edgeRequest, .suspended⟩ ∧
      edgeRunning.edges.cells 0 = some ⟨edgeRequest, .evaluating⟩ ∧
      edgeFinished.edges.cells 0 = some ⟨edgeRequest, .returned row⟩ ∧
      EdgeMass (initialBound heap) ⟨edgeRequest, .suspended⟩ ∧
      EdgeMass (initialBound heap) ⟨edgeRequest, .evaluating⟩ ∧
      EdgeMass (initialBound heap) ⟨edgeRequest, .returned row⟩ ∧
      lookupEdge 8 edgeRequest edgeFinished = (0, edgeFinished) ∧
      demandEdge 0 edgeFinished = (.ready row, edgeFinished) ∧
      SourceRecursiveIntersectionSourceProfile.edgeRead heap row.entry.identity = some row ∧
      InternedValueMass.edge row ≤ initialBound heap ∧
      row.children.length = 2 ∧
      1 + InternedValueMass.values row.children ≤ initialBound heap ∧
      row.children.length < initialBound heap ∧
      (∀ child ∈ row.children, InternedValueMass.value child < initialBound heap) ∧
      SourceCurrentAllocatedNativePhysicalCache.Valid edgeFinished := by
  have safe : SourceRecursiveIntersectionEdgeMemo.KeySafe 8 edgeRequest.domain edgeRequest.left edgeRequest.right := by
    unfold SourceRecursiveIntersectionEdgeMemo.KeySafe
    decide
  have published := SourceCurrentAllocatedNativePhysicalCache.lookupEdge_valid nodeFinished node_finished_valid edgeRequest (by simpa only [nodeFinished_machine] using edge_ready) safe
  have running := SourceCurrentAllocatedNativePhysicalCache.demandEdge_valid edgePublished published 0
  have first : edgePublished.edges.cells 0 = some ⟨edgeRequest, .suspended⟩ := by cbv
  have second : edgeRunning.edges.cells 0 = some ⟨edgeRequest, .evaluating⟩ := by cbv
  have last : edgeFinished.edges.cells 0 = some ⟨edgeRequest, .returned row⟩ := by cbv
  have final := SourceCurrentAllocatedNativePhysicalCache.finishEdge_valid edgeRunning running 0 edgeRequest row second (by simpa only [edgeRunning_machine, machine] using resident)
  have stored := InternedValueMassHeap.initial heap heap_facts
  have firstMass := edge_cell edgePublished published (by simpa only [edgePublished_machine, machine] using stored) 0 _ first
  have secondMass := edge_cell edgeRunning running (by simpa only [edgeRunning_machine, machine] using stored) 0 _ second
  have lastMass := edge_cell edgeFinished final (by simpa only [edgeFinished_machine, machine] using stored) 0 _ last
  have found := SourceRecursiveIntersectionSourceProfile.resident_read heap heap_facts row resident
  have bounded := edge_read_bound heap stored row.entry.identity row found
  have children := resident_children heap stored row resident
  refine ⟨rfl, by cbv, first, second, last, firstMass, secondMass, lastMass,
    ?_, ?_, found, bounded, ?_, children.1, children.2.1, children.2.2, final⟩ <;> cbv

#print axioms constructed_node_warm
#check @constructed_node_warm
#print axioms constructed_edge_warm
#check @constructed_edge_warm
end MicroCFTA.PhysicalMassKernels
