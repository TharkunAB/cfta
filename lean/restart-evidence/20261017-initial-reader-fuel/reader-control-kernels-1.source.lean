import MicroCFTA.SourceCurrentAllocatedReaderControl
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.ReaderControlKernels
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedReaderControl
private def expression : InternedNestedConstruction.Syntax Nat Bool :=
  .node [.mk 9 true [
    .binder true (.node [.mk 0 true [.var 0], .mk 1 true []]),
    .union [.binder true (.node [.mk 0 true [.var 0], .mk 1 true []]), .node [.mk 2 true []]]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def recursive := (children root).getD 0 .empty
private def alternatives := (children root).getD 1 .empty
private def unfolded := InternedFreshOrdinaryStoredSubstitution.unfold recursive heap
private def result : Value Nat Bool := match unfolded with | .done value _ => value | .pending .. => .empty
private def nextHeap := unfolded.state
private def ownName := (MergedSourceComparison.identity recursive).getD 0
private def unionName := (MergedSourceComparison.identity alternatives).getD 0
private def members := match alternatives with | .union _ values _ _ => values | _ => []
private def sourceMass := InternedValueMassHeap.initialBound heap
private def limit := MergedPhysicalWarmup.maximumDepth (MergedPhysicalWarmup.nodeInventory heap) + 1

private def first : Config Nat Bool := ⟨heap, [], [recursive, recursive]⟩
private def running : Config Nat Bool := ⟨nextHeap, [ownName], [result, recursive]⟩
private def popped : Config Nat Bool := ⟨nextHeap, [ownName], [recursive]⟩
private def finished : Config Nat Bool := ⟨nextHeap, [ownName], []⟩
private def initialQ := initialBound sourceMass heap first.pending
private def unionFirst : Config Nat Bool := ⟨heap, [], [alternatives]⟩
private def unionNext : Config Nat Bool := ⟨heap, [unionName], members⟩
private def unionVisited : Config Nat Bool := ⟨heap, [unionName], [alternatives]⟩
private def unionDone : Config Nat Bool := ⟨heap, [unionName], []⟩
private def unionQ := initialBound sourceMass heap unionFirst.pending

private theorem constructed : built = .done root heap := by cbv
private theorem actual : InternedFreshOrdinaryStoredSubstitution.unfold recursive heap = .done result nextHeap := by cbv
private theorem semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap heap :=
  SourceRecursiveIntersectionSemanticHeap.constructed expression root heap constructed
private theorem sourceCovered : InternedRecordCoherence.Covered [] heap :=
  InternedFreshOrdinaryCoverage.closed_covered expression root heap constructed
private theorem sourceDepth : InternedOpenDepthReadback.Heap heap := by
  simpa only [constructed, InternedNestedConstruction.Outcome.state] using InternedOpenDepthExecution.closed_heap expression
private theorem stored : InternedValueMassHeap.Stored sourceMass heap := InternedValueMassHeap.initial heap semantic.1.normal.facts
private theorem children_eq : children root = [recursive, alternatives] := by cbv
private theorem recursiveAvailable : Available heap recursive := by
  have known := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  exact known.children recursive (by rw [children_eq]; exact List.mem_cons_self)
private theorem unionAvailable : Available heap alternatives := by
  have known := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  exact known.children alternatives (by rw [children_eq]; exact List.mem_cons_of_mem _ List.mem_cons_self)
private theorem firstGood : Good limit first := by
  refine ⟨semantic, sourceCovered, sourceDepth, InternedMuDepthInventory.initial_bounded heap semantic.1.normal.facts, ?_, ?_⟩
  · intro value member
    simp only [first, List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst value
    exact recursiveAvailable
  · intro value member
    simp only [first, List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst value
    cbv
private theorem firstFits : Fits initialQ first := initial_fits heap [] [recursive, recursive] sourceMass stored firstGood.available
private theorem firstStep : Step first running := .mu_fresh (by simp) actual
private theorem secondStep : Step running popped := .node
private theorem thirdStep : Step popped finished := .mu_seen (by simp)

/-- A source-built recursive collector unfolds, emits ordinary rows, then skips its visited Mu. -/
theorem actual_mu_control :
    built = .done root heap ∧ Step first running ∧ Step running popped ∧ Step popped finished ∧
    Good limit finished ∧ Fits (g (g (g initialQ))) finished ∧
    HeightOrder.VectorBelow (limit + 1) (measure limit running) (measure limit first) ∧
    (∀ index, measure limit finished index ≤ g (g (g initialQ))) ∧
    heap.nodes.next < nextHeap.nodes.next ∧ heap.edges.next < nextHeap.edges.next := by
  have oneGood := firstStep.good firstGood
  have twoGood := secondStep.good oneGood
  have finalGood := thirdStep.good twoGood
  have oneFits := firstStep.fits firstGood firstFits
  have twoFits := secondStep.fits oneGood oneFits
  have finalFits := thirdStep.fits twoGood twoFits
  exact ⟨constructed, firstStep, secondStep, thirdStep, finalGood, finalFits,
    firstStep.decreases firstGood, fun index => measure_le finalFits index, by cbv, by cbv⟩

private theorem unionGood : Good limit unionFirst := by
  refine ⟨semantic, sourceCovered, sourceDepth, InternedMuDepthInventory.initial_bounded heap semantic.1.normal.facts, ?_, ?_⟩
  · intro value member
    have same : value = alternatives := by simpa only [unionFirst, List.mem_singleton] using member
    subst value
    exact unionAvailable
  · intro value member
    have same : value = alternatives := by simpa only [unionFirst, List.mem_singleton] using member
    subst value
    cbv
private theorem unionFits : Fits unionQ unionFirst := initial_fits heap [] [alternatives] sourceMass stored unionGood.available
private theorem freshUnion : Step unionFirst unionNext := .union_fresh (by simp)
private theorem visitedUnion : Step unionVisited unionDone := .union_seen (by simp)

/-- Real union expansion and visited replay use the same original heap and derived local bounds. -/
theorem actual_union_control :
    Step unionFirst unionNext ∧ Good limit unionNext ∧ Fits (g unionQ) unionNext ∧
    HeightOrder.VectorBelow (limit + 1) (measure limit unionNext) (measure limit unionFirst) ∧
    Step unionVisited unionDone ∧ Good limit unionDone ∧ Fits (g unionQ) unionDone := by
  have visitedGood : Good limit unionVisited :=
    ⟨unionGood.semantic, unionGood.covered, unionGood.depth, unionGood.bounded, unionGood.available, unionGood.closed⟩
  have visitedFits : Fits unionQ unionVisited := ⟨unionFits.stored, unionFits.nodes, unionFits.edges, unionFits.work⟩
  exact ⟨freshUnion, freshUnion.good unionGood, freshUnion.fits unionGood unionFits, freshUnion.decreases unionGood,
    visitedUnion, visitedUnion.good visitedGood, visitedUnion.fits visitedGood visitedFits⟩

end MicroCFTA.ReaderControlKernels

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#print axioms MicroCFTA.ReaderControlKernels.actual_mu_control
#check @MicroCFTA.ReaderControlKernels.actual_mu_control
#print axioms MicroCFTA.ReaderControlKernels.actual_union_control
#check @MicroCFTA.ReaderControlKernels.actual_union_control
