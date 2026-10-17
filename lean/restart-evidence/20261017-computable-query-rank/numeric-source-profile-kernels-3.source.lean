import MicroCFTA.SourceRecursiveIntersectionNumericSourceProfile
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

namespace MicroCFTA.NumericSourceProfileKernels
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome)
open SourceRecursiveIntersectionNumericSourceProfile
open SourceRecursiveIntersectionSourceProfile

private def plan : Syntax Nat Bool := .union [
  .binder false (.node [.mk 0 true [.var 0]]),
  .node [.mk 1 false [], .mk 2 true [.node [.mk 3 true []], .node [.mk 3 true []]]]]
private def built := InternedFreshOrdinaryConstruction.build plan [] empty
private def source := built.state
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def rootId := (SourcePreparedSharedRows.reference root).getD 0
private def mass := InternedValueMassHeap.initialBound source
private def extended := run (makeEdge (99 : Nat) false [root, root]) source
private def laterMass := max mass (1 + InternedValueMass.values [root, root])

private theorem constructed : built = .done root source := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete plan
  simp only [built, root, source, done, Outcome.state]

private theorem source_facts : Facts source := (InternedFreshOrdinaryFacts.closed_verified plan).facts
private theorem root_available : Available source root :=
  (InternedFreshOrdinaryFacts.closed_verified plan).result root source constructed

/-- A recursive source supplies numeric branching and mass bounds before and after actual duplicated-child work. -/
theorem recursive_source_and_growth :
    built = .done root source ∧ Facts source ∧ memberCount root = 2 ∧
    (∃ entry body depth ordinary, (children root)[0]? = some (.mu entry body depth ordinary)) ∧
    InternedValueMassHeap.Stored mass source ∧
    (limits source).rows ≤ source.nodes.next * mass ∧
    (limits source).members ≤ source.nodes.next * mass ∧
    (limits source).arity ≤ source.edges.next * mass ∧
    InternedValueMassHeap.initialBound source ≤ 1 + (source.nodes.next + source.edges.next) * mass ∧
    SourceRecursiveIntersectionInstructionProfile.sourceBranching source ≤ branching source.nodes.next source.edges.next mass ∧
    Grows source extended.2 ∧ Extends source.nodes.issued extended.2.nodes.issued ∧
    SourcePreparedSharedRows.read extended.2 rootId = some root ∧
    (nodeEdges root).length ≤ source.nodes.next * mass ∧ memberCount root ≤ source.nodes.next * mass ∧
    InternedValueMassHeap.Stored laterMass extended.2 ∧
    InternedValueMassHeap.initialBound extended.2 ≤
      1 + (extended.2.nodes.next + extended.2.edges.next) * laterMass ∧
    SourceRecursiveIntersectionInstructionProfile.sourceBranching extended.2 ≤
      branching extended.2.nodes.next extended.2.edges.next laterMass := by
  have stored := InternedValueMassHeap.initial source source_facts
  have limits := limits_bound source stored
  have physical := edge_verified (99 : Nat) false [root, root] source source_facts (by
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · exact root_available
    · cases List.mem_singleton.mp later
      exact root_available)
  have produced := InternedValueMassConstructors.edge (99 : Nat) false [root, root] source stored
  have recorded : SourcePreparedSharedRows.reference root = some rootId := by cbv
  have read := SourcePreparedSharedRows.read_identity source source_facts root root_available rootId recorded
  have retained := SourceCurrentConstrainedCapSourceWeightTransport.read_grows source extended.2
    physical.growth physical.history rootId root read
  have profile := SourceRecursiveIntersectionSourceProfile.read_current source extended.2 source_facts
    physical.growth physical.history rootId root root read retained
  exact ⟨constructed, source_facts, by cbv, ⟨_, _, _, _, by cbv⟩,
    stored, limits.1, limits.2.1, limits.2.2, initial_bound source stored, source_branching source stored,
    physical.growth, physical.history, retained, Nat.le_trans profile.2.1.1 limits.1,
    Nat.le_trans profile.2.1.2 limits.2.1, produced.1,
    initial_bound extended.2 produced.1, source_branching extended.2 produced.1⟩

private def constantPlan : Syntax Nat Bool := .node [.mk 0 true []]
private def constantEdge := run (makeEdge (0 : Nat) true []) (empty : State Nat Bool)
private def constantNode := run (makeNode [constantEdge.1]) constantEdge.2

/-- A real three-unit stored payload bound does not bound the recomputed five-unit initial sum. -/
theorem stored_mass_is_not_initial_sum :
    InternedFreshOrdinaryConstruction.build constantPlan [] empty = .done constantNode.1 constantNode.2 ∧
    Facts constantNode.2 ∧ InternedValueMassHeap.Stored 3 constantNode.2 ∧
    InternedValueMassHeap.initialBound constantNode.2 = 5 ∧
    ¬ InternedValueMassHeap.initialBound constantNode.2 ≤ 3 ∧
    InternedValueMassHeap.initialBound constantNode.2 ≤
      1 + (constantNode.2.nodes.next + constantNode.2.edges.next) * 3 := by
  have built : InternedFreshOrdinaryConstruction.build constantPlan [] empty = .done constantNode.1 constantNode.2 := by cbv
  have verified := InternedFreshOrdinaryFacts.closed_verified constantPlan
  have facts : Facts constantNode.2 := by simpa only [built, Outcome.state] using verified.facts
  have row := InternedValueMassConstructors.edge (0 : Nat) true [] (empty : State Nat Bool)
    (InternedValueMassHeap.empty_stored (by decide : 1 ≤ 1))
  have node := InternedValueMassConstructors.node [constantEdge.1] constantEdge.2 row.1
  have numeric : max (max 1 (1 + InternedValueMass.values ([] : List (Value Nat Bool))))
      (1 + InternedValueMass.edges [constantEdge.1]) = 3 := by cbv
  have stored : InternedValueMassHeap.Stored 3 constantNode.2 := by
    simpa only [numeric] using node.1
  exact ⟨built, facts, stored, by cbv, by cbv, initial_bound constantNode.2 stored⟩

#print axioms recursive_source_and_growth
#check @recursive_source_and_growth
#print axioms stored_mass_is_not_initial_sum
#check @stored_mass_is_not_initial_sum
end MicroCFTA.NumericSourceProfileKernels
