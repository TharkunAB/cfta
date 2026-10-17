import MicroCFTA.InternedValueMassConstructors
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
set_option cbv.maxSteps 100000000

namespace MicroCFTA.HeapMassKernels
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome)
open InternedValueMassHeap

private def plan : Syntax Nat Bool := .union [
  .binder false (.node [.mk 0 true [.var 0]]),
  .node [.mk 1 false [], .mk 2 true [.node [.mk 3 true []], .node [.mk 3 true []]]]]
private def built := InternedFreshOrdinaryConstruction.build plan [] empty
private def source := built.state
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def firstEdge := run (makeEdge (99 : Nat) false [root, root]) source
private def firstNode := run (makeNode [firstEdge.1, firstEdge.1]) firstEdge.2
private def edgeBound := max (initialBound source) (1 + InternedValueMass.values [root, root])
private def nodeBound := max edgeBound (1 + InternedValueMass.edges [firstEdge.1, firstEdge.1])

private theorem constructed : built = .done root source := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete plan
  simp only [built, root, source, done, Outcome.state]

private theorem source_facts : Facts source :=
  (InternedFreshOrdinaryFacts.closed_verified plan).facts

private theorem root_available : Available source root :=
  (InternedFreshOrdinaryFacts.closed_verified plan).result root source constructed

/-- A source-built recursive heap supplies its own mass store before duplicated-child and duplicated-row work, then exact warm reuse. -/
theorem constructed_store_and_warm_node :
    InternedFreshOrdinaryConstruction.build plan [] empty = .done root source ∧
      SourceRecursiveIntersectionSourceProfile.memberCount root = 2 ∧
      Stored (initialBound source) source ∧ InternedValueMass.value root ≤ initialBound source ∧
      Stored edgeBound firstEdge.2 ∧ InternedValueMass.edge firstEdge.1 ≤ edgeBound ∧
      Stored nodeBound firstNode.2 ∧ InternedValueMass.value firstNode.1 ≤ nodeBound ∧
      run (makeNode [firstEdge.1, firstEdge.1]) firstNode.2 = (firstNode.1, firstNode.2) ∧
      Grows source firstNode.2 := by
  have stored := initial source source_facts
  have rootBound := available source stored root root_available
  have row := InternedValueMassConstructors.edge (99 : Nat) false [root, root] source stored
  have node := InternedValueMassConstructors.node [firstEdge.1, firstEdge.1] firstEdge.2 row.1
  have rowPhysical := InternedConstructorTemplates.run_correct (makeEdge (99 : Nat) false [root, root])
    source source_facts.coherent.valid
  have nodePhysical := InternedConstructorTemplates.run_correct (makeNode [firstEdge.1, firstEdge.1])
    firstEdge.2 rowPhysical.1
  have repeated :=  InternedConstructorTemplates.replay (makeNode [firstEdge.1, firstEdge.1])
    firstEdge.2 firstNode.2 rowPhysical.1 (grows_refl _)
  have shape : SourceRecursiveIntersectionSourceProfile.memberCount root = 2 := by cbv
  exact ⟨constructed, shape, stored, rootBound, row.1, row.2, node.1, node.2, repeated,
    grows_trans rowPhysical.2 nodePhysical.2⟩

private def localName : InternedBinderProtocol.Reference := .intersection 17 19
private def combined := run (makeUnion [.reference localName, root]) source
private def combinedBound := max (initialBound source)
  (1 + InternedValueMass.values [.reference localName, root])

/-- Actual root normalization removes its own added reference and keeps the same produced store bound at the exact returned heap. -/
theorem actual_filter_keeps_bound :
    InternedFreshOrdinaryConstruction.build plan [] empty = .done root source ∧
      Stored (initialBound source) source ∧
      Stored combinedBound combined.2 ∧ InternedValueMass.value combined.1 ≤ combinedBound ∧
      run (withoutSelfReference localName combined.1) combined.2 = (root, combined.2) ∧
      Stored combinedBound (run (withoutSelfReference localName combined.1) combined.2).2 ∧
      InternedValueMass.value (run (withoutSelfReference localName combined.1) combined.2).1 ≤ combinedBound ∧
      InternedValueMass.value (cleanup root) ≤ combinedBound := by
  have stored := initial source source_facts
  have union := InternedValueMassConstructors.union [.reference localName, root] source stored
  have normalized := InternedValueMassConstructors.filter localName combined.1 combined.2 union.1 union.2
  have exactReturn : run (withoutSelfReference localName combined.1) combined.2 = (root, combined.2) := by cbv
  have rootBound := available source stored root root_available
  have cleanup := Nat.le_trans (InternedValueMassConstructors.cleanup_le root) rootBound
  exact ⟨constructed, stored, union.1, union.2, exactReturn, normalized.1, normalized.2,
    Nat.le_trans cleanup (Nat.le_max_left _ _)⟩

#print axioms constructed_store_and_warm_node
#check @constructed_store_and_warm_node
#print axioms actual_filter_keeps_bound
#check @actual_filter_keeps_bound
end MicroCFTA.HeapMassKernels
