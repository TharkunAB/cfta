import MicroCFTA.SourceRecursiveIntersectionSourceProfile
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReservations

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

namespace MicroCFTA.SourceProfileKernels
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome)
open SourceRecursiveIntersectionSourceProfile

private def plan : Syntax Nat Bool := .union [
  .binder false (.node [.mk 0 true [.var 0]]),
  .node [.mk 1 false [], .mk 2 true [.node [.mk 3 true []], .node [.mk 3 true []]]]]
private def built := InternedFreshOrdinaryConstruction.build plan [] empty
private def source := built.state
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def muPayload : Value Nat Bool := (SourcePreparedSharedRows.read source 2).getD .empty
private def extraEdge := run (makeEdge (99 : Nat) true []) source
private def extraNode := run (makeNode [extraEdge.1]) extraEdge.2
private def later := extraNode.2
private def extension : Work Nat Bool (Value Nat Bool) :=
  (makeEdge (99 : Nat) true []).bind fun edge => makeNode [edge]

private theorem constructed : built = .done root source := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete plan
  simp only [built, root, source, done, Outcome.state]

private theorem source_facts : Facts source :=
  (InternedFreshOrdinaryFacts.closed_verified plan).facts

private theorem root_available : Available source root :=
  (InternedFreshOrdinaryFacts.closed_verified plan).result root source constructed

private theorem actual_profile :
    (limits source).rows = 6 ∧ (limits source).members = 2 ∧ (limits source).arity = 5 ∧ memberCount root = 2 := by
  cbv

private theorem mu_read : SourcePreparedSharedRows.read source 2 = some muPayload := by
  cbv

private theorem mu_shape : ∃ entry body depth ordinary, muPayload = .mu entry body depth ordinary := by
  have tag : (match muPayload with | .mu .. => true | _ => false) = true := by cbv
  cases selected : muPayload with
  | mu entry body depth ordinary => exact ⟨entry, body, depth, ordinary, rfl⟩
  | empty | reference | node | union => simp only [selected, Bool.false_eq_true] at tag

private theorem mu_member : muPayload ∈ InternedProbeProvenance.children root := by
  have selected : (InternedProbeProvenance.children root)[0]? = some muPayload := by cbv
  exact List.mem_of_getElem? selected

/-- An actual recursive source union retains its old row, member, arity, and syntax bounds after new constructor requests. -/
theorem recursive_source_growth :
    ∃ entry body depth ordinary,
      InternedFreshOrdinaryConstruction.build plan [] empty = .done root source ∧
      SourcePreparedSharedRows.read source 2 = some (.mu entry body depth ordinary) ∧
      (.mu entry body depth ordinary) ∈ InternedProbeProvenance.children root ∧
      (limits source).rows = 6 ∧ (limits source).members = 2 ∧ (limits source).arity = 5 ∧
      memberCount root = 2 ∧ Node (limits source) root ∧
      Node (limits source) body ∧ Node (limits source) depth ∧ Node (limits source) ordinary ∧
      run extension source = (extraNode.1, later) ∧ Grows source later ∧
      Extends source.nodes.issued later.nodes.issued ∧ Extends source.edges.issued later.edges.issued ∧
      (∀ number value, SourcePreparedSharedRows.read source number = some value →
        SourcePreparedSharedRows.read later number = some value ∧ Node (limits source) value ∧ sizeOf value ≤ nodeSize source) ∧
      (∀ edge, EdgeResident source edge → edgeRead later edge.entry.identity = some edge ∧
        Edge (limits source) edge ∧ sizeOf edge ≤ edgeSize source) := by
  obtain ⟨entry, bodyValue, depth, ordinary, shape⟩ := mu_shape
  have muAvailable : Available source (.mu entry bodyValue depth ordinary) := by
    rw [← shape]
    exact SourcePreparedSharedRows.read_available source source_facts 2 muPayload mu_read
  have edge := InternedNestedFacts.edge_verified (99 : Nat) true [] source source_facts
    (by intro value member; cases member)
  have node := InternedNestedFacts.node_verified [extraEdge.1] extraEdge.2 edge.facts
    (by intro value member; exact List.mem_singleton.mp member ▸ edge.result _ _ rfl)
  have growth : Grows source later := grows_trans edge.growth node.growth
  have history : Extends source.nodes.issued later.nodes.issued := extends_trans edge.history node.history
  have execution : run extension source = (extraNode.1, later) := by
    simp only [extension, run_bind]
    rfl
  have edgesHistory : Extends source.edges.issued later.edges.issued := by
    have both := SourceCurrentAllocatedFiniteOrdinaryReservations.run_issued extension source source_facts.coherent.valid
    simpa only [execution] using both.2
  refine ⟨entry, bodyValue, depth, ordinary, constructed, shape ▸ mu_read, shape ▸ mu_member,
    actual_profile.1, actual_profile.2.1, actual_profile.2.2.1, actual_profile.2.2.2,
    available source source_facts root root_available,
    child source source_facts _ muAvailable bodyValue (by simp [InternedProbeProvenance.children]),
    child source source_facts _ muAvailable depth (by simp [InternedProbeProvenance.children]),
    child source source_facts _ muAvailable ordinary (by simp [InternedProbeProvenance.children]),
    execution, growth, history, edgesHistory, ?_, ?_⟩
  · intro number value found
    have retained := SourceCurrentConstrainedCapSourceWeightTransport.read_grows source later growth history number value found
    have bounded := read_current source later source_facts growth history number value value found retained
    exact ⟨retained, bounded.2⟩
  · intro row resident
    have captured := resident_read source source_facts row resident
    have retained := edge_read_grows source later growth edgesHistory _ row captured
    have bounded := edge_read_current source later source_facts growth edgesHistory _ row row captured retained
    exact ⟨retained, bounded.2⟩

private def hole : State Nat Bool :=
  {empty with nodes := (Cache.intern (empty : State Nat Bool).nodes (.node [0])).2}
private def firstEdge := run (makeEdge (0 : Nat) false []) (empty : State Nat Bool)
private def firstNode := run (makeNode [firstEdge.1]) firstEdge.2

/-- Pending reservations add no payload count, and an absent identity can later gain a larger source profile. -/
theorem absent_payload_boundary :
    Facts hole ∧ hole.nodes.next = 1 ∧ SourcePreparedSharedRows.read hole 0 = none ∧
      nodePayloads hole = [] ∧ (limits hole).rows = 0 ∧
      SourcePreparedSharedRows.read (empty : State Nat Bool) 0 = none ∧
      SourcePreparedSharedRows.read firstNode.2 0 = some firstNode.1 ∧
      Node (limits firstNode.2) firstNode.1 ∧ ¬Node (limits (empty : State Nat Bool)) firstNode.1 := by
  have pending : Facts hole := InternedNestedFacts.reserve_facts (.node [0]) (empty : State Nat Bool) empty_facts
  have edge := InternedNestedFacts.edge_verified (0 : Nat) false [] (empty : State Nat Bool) empty_facts
    (by intro value member; cases member)
  have node := InternedNestedFacts.node_verified [firstEdge.1] firstEdge.2 edge.facts
    (by intro value member; exact List.mem_singleton.mp member ▸ edge.result _ _ rfl)
  have returned : Available firstNode.2 firstNode.1 := node.result _ _ rfl
  refine ⟨pending, rfl, rfl, rfl, rfl, rfl, ?_, available firstNode.2 node.facts firstNode.1 returned, ?_⟩
  · cbv
  · intro bounded
    have impossible := bounded.1
    have count : (nodeEdges firstNode.1).length = 1 := by cbv
    rw [count] at impossible
    change 1 ≤ 0 at impossible
    omega

#print axioms recursive_source_growth
#check @recursive_source_growth
#print axioms absent_payload_boundary
#check @absent_payload_boundary
end MicroCFTA.SourceProfileKernels
