import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstructionReservations
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryKeys

namespace MicroCFTA.ConstructionReservationIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open SourceCurrentAllocatedFiniteOrdinaryConstructionReservations

private def duplicateRows : Syntax Nat Unit := .node [.mk 7 () [], .mk 7 () []]
private def duplicateBuild : Value Nat Unit × State Nat Unit :=
  run ((makeEdge 7 () []).bind fun first =>
    (makeEdge 7 () []).bind fun second => makeNode [first, second]) empty

/-- Static syntax counts repeated row occurrences although their actual identities coincide. -/
theorem duplicate_source_rows :
    nodeCount duplicateRows = 1 ∧ edgeCount duplicateRows = 2 ∧
    InternedFreshOrdinaryConstruction.build duplicateRows [] empty = .done duplicateBuild.1 duplicateBuild.2 ∧
    duplicateBuild.2.nodes.next = 1 ∧ duplicateBuild.2.edges.next = 1 ∧
    SourceCurrentAllocatedFiniteOrdinaryDomain.Node duplicateBuild.1 ∧
    Available duplicateBuild.2 duplicateBuild.1 := by
  have admitted : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node duplicateRows :=
    .ordinary (.cons .nil (.cons .nil .nil))
  obtain ⟨value, after, actual, domain, facts, available, nodes, edges⟩ := closed duplicateRows admitted
  have same : InternedFreshOrdinaryConstruction.build duplicateRows [] empty =
      .done duplicateBuild.1 duplicateBuild.2 := by
    simp only [duplicateRows, InternedFreshOrdinaryConstruction.build,
      InternedFreshOrdinaryConstruction.buildEdges, InternedFreshOrdinaryConstruction.buildMany,
      Outcome.bind, work, duplicateBuild, run_bind]
  obtain ⟨rfl, rfl⟩ := Outcome.done.inj (actual.symm.trans same)
  refine ⟨by simp [nodeCount, counts, countsRows, countsMany, duplicateRows],
    by simp [edgeCount, counts, countsRows, countsMany, duplicateRows], same, ?_, ?_, domain, available⟩ <;>
    simp [duplicateBuild, makeEdge, makeNode, surviving, canonicalEdges, EnumerationBuilderCaches.canonicalIds,
      run, Work.bind, edgeStep, nodeStep, Cache.intern, Cache.install, Cache.reserve, Cache.keepFirst,
      Cache.put, empty, Cache.emptyState, identifyNode, maximumDepth, childFree, canonicalFree,
      Value.referenceOf, EdgeValue.children, EdgeValue.entry, List.eraseDups_cons]

/-- An unavailable lexical index still completes without consuming an identity. -/
theorem missing_variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (index : Nat) :
    ∃ value after, InternedFreshOrdinaryConstruction.build (.var index) [] state = .done value after ∧
      value = .empty ∧ after = state ∧
      after.nodes.next ≤ state.nodes.next + nodeCount (Syntax.var (Symbol := Symbol) (Guard := Guard) index) ∧
      after.edges.next ≤ state.edges.next + edgeCount (Syntax.var (Symbol := Symbol) (Guard := Guard) index) := by
  obtain ⟨value, after, actual, nodes, edges⟩ := complete (.var index) (.var index) [] state
  have selected : InternedFreshOrdinaryConstruction.build (Syntax.var index) [] state = .done .empty state := by
    simp [InternedFreshOrdinaryConstruction.build]
  obtain ⟨sameValue, sameHeap⟩ := Outcome.done.inj (actual.symm.trans selected)
  exact ⟨value, after, actual, sameValue, sameHeap, nodes, edges⟩

/-- Two source constructions thread the actual warm heap and add only syntax resource bounds. -/
theorem two_constructions {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (admitted : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression) :
    ∃ first middle second after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done first middle ∧
      InternedFreshOrdinaryConstruction.build expression [] middle = .done second after ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Node first ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Node second ∧
      Available middle first ∧ Available after second ∧
      after.nodes.next ≤ nodeCount expression + nodeCount expression ∧
      after.edges.next ≤ edgeCount expression + edgeCount expression := by
  obtain ⟨first, middle, actual, domain, facts, available, nodes, edges⟩ := closed expression admitted
  obtain ⟨second, after, next, nextDomain, nextFacts, nextAvailable, moreNodes, moreEdges⟩ :=
    build expression admitted [] middle facts (by intro value member; cases member) .nil
  refine ⟨first, middle, second, after, actual, next, domain, nextDomain, available, nextAvailable, ?_, ?_⟩ <;> omega

/-- Initial-only syntax bounds derive the actual constructed root's recursive native keys. -/
theorem source_keys {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (admitted : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (bits : Nat) (nodesFit : nodeCount expression ≤ 2 ^ bits)
    (edgesFit : edgeCount expression ≤ 2 ^ (bits + 2)) :
    ∃ value after, InternedFreshOrdinaryConstruction.build expression [] empty = .done value after ∧
      Available after value ∧ SourceCurrentAllocatedFiniteOrdinaryKeys.Node bits value := by
  obtain ⟨value, after, actual, domain, facts, available, nodes, edges⟩ := closed expression admitted
  refine ⟨value, after, actual, available,
    SourceCurrentAllocatedFiniteOrdinaryKeys.of_available bits after facts.coherent facts.linked
      (Nat.le_trans nodes nodesFit) (Nat.le_trans edges edgesFit) value available domain⟩

/-- A supplied actual warm return has the same input-only bound without a readiness oracle. -/
theorem supplied_actual {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (admitted : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryConstruction.build expression environment before = .done value after)
    (bits : Nat) (nodesFit : before.nodes.next + nodeCount expression ≤ 2 ^ bits)
    (edgesFit : before.edges.next + edgeCount expression ≤ 2 ^ (bits + 2)) :
    after.nodes.next ≤ 2 ^ bits ∧ after.edges.next ≤ 2 ^ (bits + 2) := by
  have bounded := build_bounds expression admitted environment before value after actual
  exact ⟨Nat.le_trans bounded.1 nodesFit, Nat.le_trans bounded.2 edgesFit⟩

end MicroCFTA.ConstructionReservationIntegration

#print axioms MicroCFTA.ConstructionReservationIntegration.duplicate_source_rows
#check @MicroCFTA.ConstructionReservationIntegration.duplicate_source_rows
#print axioms MicroCFTA.ConstructionReservationIntegration.missing_variable
#check @MicroCFTA.ConstructionReservationIntegration.missing_variable
#print axioms MicroCFTA.ConstructionReservationIntegration.two_constructions
#check @MicroCFTA.ConstructionReservationIntegration.two_constructions
#print axioms MicroCFTA.ConstructionReservationIntegration.source_keys
#check @MicroCFTA.ConstructionReservationIntegration.source_keys
#print axioms MicroCFTA.ConstructionReservationIntegration.supplied_actual
#check @MicroCFTA.ConstructionReservationIntegration.supplied_actual
