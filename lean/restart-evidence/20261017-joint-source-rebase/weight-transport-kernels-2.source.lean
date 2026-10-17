import MicroCFTA.SourceCurrentConstrainedCapSourceWeightTransport

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.WeightTransportIndependent
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedRecordCoherence InternedDeepFreeDepth
open SourceCurrentConstrainedCapPairOccurrences (sourceWeight identityWeight Classified FreeLE FreeBelow)
open SourceCurrentConstrainedCapSourceWeightTransport
open SourceRecursiveIntersectionResultScope (Scope)

private def plain (guard : Bool) : Prop := guard = true
private def badEdge := run (makeEdge (0 : Nat) false []) (empty : State Nat Bool)
private def badNode := run (makeNode [badEdge.1]) badEdge.2
private def source := badNode.2
private def localName : InternedBinderProtocol.Reference := .intersection 0 0
private def leaf : Value Nat Bool := .reference localName
private def resultEdge := run (makeEdge (1 : Nat) true [leaf]) source
private def resultNode := run (makeNode [resultEdge.1]) resultEdge.2
private def later := resultNode.2
private def result := resultNode.1
private noncomputable def bound := sourceWeight plain source localName + 1

private theorem source_read : SourcePreparedSharedRows.read source 0 = some badNode.1 := by cbv
private theorem edge_children : resultEdge.1.children = [leaf] := by cbv
private theorem actual_deep : localName ∈ deepNames result := by
  cbv
  exact List.mem_cons_self

private theorem initial_facts : Facts source := by
  have edge := InternedNestedFacts.edge_verified (0 : Nat) false [] (empty : State Nat Bool) empty_facts
    (by intro value member; cases member)
  have resident : ∀ value ∈ [badEdge.1], EdgeResident badEdge.2 value := by
    intro value member
    exact List.mem_singleton.mp member ▸ edge.result _ _ rfl
  exact (InternedNestedFacts.node_verified [badEdge.1] badEdge.2 edge.facts resident).facts

/-- Actual new constructor writes retain a nonzero deep occurrence's earlier represented weight and classifier. -/
theorem actual_deep_constructor_transport :
    Grows source later ∧ Extends source.nodes.issued later.nodes.issued ∧
      Supported source [(0, 0)] ∧ SourcePreparedSharedRows.read later 0 = some badNode.1 ∧
      localName ∈ deepNames result ∧ Available later result ∧ Scope [(0, 0)] result ∧
      Classified (sourceWeight plain source) bound result ∧
      Classified (sourceWeight plain later) bound result ∧
      sourceWeight plain later localName = sourceWeight plain source localName := by
  have localAvailable : Available source leaf := reference_available source localName (by intro number member; simp [Value.free, localName] at member)
  have edge := InternedNestedFacts.edge_verified (1 : Nat) true [leaf] source initial_facts
    (by intro value member; exact List.mem_singleton.mp member ▸ localAvailable)
  have resident : ∀ value ∈ [resultEdge.1], EdgeResident resultEdge.2 value := by
    intro value member
    exact List.mem_singleton.mp member ▸ edge.result _ _ rfl
  have node := InternedNestedFacts.node_verified [resultEdge.1] resultEdge.2 edge.facts resident
  have growth : Grows source later := grows_trans edge.growth node.growth
  have history : Extends source.nodes.issued later.nodes.issued := extends_trans edge.history node.history
  have supported : Supported source [(0, 0)] :=
    (supported_empty source).cons (0, 0) badNode.1 badNode.1 source_read source_read
  have localScope : Scope [(0, 0)] leaf := SourceRecursiveIntersectionResultScope.repeated [(0, 0)] (0, 0) List.mem_cons_self
  have edgeScope := SourceRecursiveIntersectionResultScope.edge [(0, 0)] (1 : Nat) true [leaf] source initial_facts
    (by intro value member; exact List.mem_singleton.mp member ▸ localAvailable)
    (by intro value member; exact List.mem_singleton.mp member ▸ localScope)
  have scope : Scope [(0, 0)] result := SourceRecursiveIntersectionResultScope.node [(0, 0)] [resultEdge.1] resultEdge.2
    edge.facts resident (by intro value member; exact List.mem_singleton.mp member ▸ edgeScope)
  have before : Classified (sourceWeight plain source) bound result := by
    apply SourceCurrentConstrainedCapPairOccurrences.makeNode (sourceWeight plain source) bound [resultEdge.1] resultEdge.2 edge.facts resident
    intro row member child inside
    have same : row = resultEdge.1 := List.mem_singleton.mp member
    subst row
    rw [edge_children] at inside
    have childSame : child = leaf := List.mem_singleton.mp inside
    subst child
    constructor
    · intro name named
      have same : name = localName := List.mem_singleton.mp named
      subst name
      exact Nat.le_succ _
    · intro name named
      have same : name = localName := List.mem_singleton.mp named
      subst name
      exact .inl (Nat.lt_succ_self _)
  have available : Available later result := node.result _ _ rfl
  exact ⟨growth, history, supported, read_grows source later growth history 0 _ source_read, actual_deep, available, scope, before,
    classified plain source later growth history _ supported result node.facts.coherent available scope bound before,
    pair_weight plain source later growth history _ supported (0, 0) List.mem_cons_self⟩

/-- An identity absent from the old source can gain positive weight after a real constructor write. -/
theorem absent_weight_boundary :
    SourcePreparedSharedRows.read (empty : State Nat Bool) 0 = none ∧
      sourceWeight plain (empty : State Nat Bool) localName = 0 ∧ 0 < sourceWeight plain source localName := by
  have notPlain : ¬ SourceEqualityAnnotationLanguage.Annotated plain badNode.1 := by
    intro annotated
    have shape : badNode.1 = .node ⟨0, .node [0]⟩ [badEdge.1] 0 [] := by cbv
    rw [shape] at annotated
    cases annotated with
    | node entry edges depth free guards children =>
        have impossible := guards badEdge.1 List.mem_cons_self
        change false = true at impossible
        cases impossible
  have positive := (SourceCurrentConstrainedCapNonplainRank.rank_pos_iff plain badNode.1).mpr notPlain
  have readWeight := SourceCurrentConstrainedCapPairOccurrences.sourceWeight_reads plain source badNode.1 badNode.1 0 0 source_read source_read
  refine ⟨rfl, rfl, ?_⟩
  change 0 < sourceWeight plain source (.intersection 0 0)
  rw [readWeight]
  unfold SourceCurrentConstrainedCapNonplainRank.pairRank
  omega

#print axioms actual_deep_constructor_transport
#check @actual_deep_constructor_transport
#print axioms absent_weight_boundary
#check @absent_weight_boundary
end MicroCFTA.WeightTransportIndependent
