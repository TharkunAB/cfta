import MicroCFTA.SourceCurrentConstrainedCapSelectedProjection

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxHeartbeats 2000000

namespace MicroCFTA.SelectedCapProjectionIntegration
open Cache InternedBinderProtocol InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityProjectionGraph SourceEqualityProjectionPathDomain
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentConstrainedCap (Cap)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- An open parent and an unrelated open root construct their selected nonhereditary endpoint. -/
theorem open_forest_own_endpoint (valid : Guard → Prop)
    (parentEntry leafEntry : Interned InternedBinderProtocol.NodeKey)
    (outerEntry : Interned (EdgeKey Symbol Guard)) (badEdge : EdgeValue Symbol Guard) (level : Nat)
    (before : State Symbol Guard) (semantic : SemanticReady before) (stored : MuStored valid before)
    (children : badEdge.children = []) (outside : ¬valid badEdge.entry.key.constraint)
    (available : Available before
      (.node parentEntry [.mk outerEntry [.node leafEntry [badEdge] 0 [], .reference (.uninterned 0)]] level [.uninterned 0])) :
    let endpoint := Value.node leafEntry [badEdge] 0 []
    let parent := Value.node parentEntry [.mk outerEntry [endpoint, .reference (.uninterned 0)]] level [.uninterned 0]
    let roots := [parent, Value.reference (.uninterned 1)]
    parent.free ≠ [] ∧ ¬MergedColdReaderClosedInputs.ClosedValues roots ∧
      ¬SourceEqualityAnnotationLanguage.Annotated valid endpoint ∧
      ∃ result after, Forest [0, 0] roots before result after ∧ SourceEqualityRequiredCache.Keeps before after ∧
        SemanticReady after ∧ Available after result ∧ result.free = [] ∧ MuStored valid after ∧ Cap valid 1 result := by
  let endpoint := Value.node leafEntry [badEdge] 0 []
  let parent := Value.node parentEntry [.mk outerEntry [endpoint, .reference (.uninterned 0)]] level [.uninterned 0]
  let roots := [parent, Value.reference (.uninterned 1)]
  have endpointCap : Cap valid 1 endpoint := by
    apply Cap.node 0
    intro child member
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, children, List.not_mem_nil] at member
  have parentCap : Cap valid 2 parent := by
    apply Cap.node 1
    intro child member
    simp only [EdgeValue.children, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact endpointCap
    · exact .plain 1 (.reference _)
  have siblingAvailable : Available before (Value.reference (.uninterned 1)) :=
    reference_available before _ (by intro number member; cases member)
  have values : Values before roots := by
    intro value member
    simp only [roots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact available
    · exact siblingAvailable
  have domain : ForestClosed [0, 0] roots := by
    simp [ForestClosed, NodeClosed, roots, parent, endpoint, select]
  have bounded : ∀ value ∈ roots, Cap valid 2 value := by
    intro value member
    simp only [roots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact parentCap
    · exact .plain 2 (.reference _)
  refine ⟨by simp [parent, Value.free], ?_, ?_, ?_⟩
  · intro allClosed
    have impossible := allClosed (Value.reference (.uninterned 1))
      (List.mem_cons_of_mem _ List.mem_cons_self)
    cases impossible
  · intro supposed
    exact outside (SourceCurrentHereditaryConstructors.node_edge supposed badEdge List.mem_cons_self).1
  · simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub] using
      SourceCurrentConstrainedCapSelectedProjection.forest_complete valid 2 [0, 0] roots before semantic values domain stored bounded

/-- Negative forest indices construct the literal missing branch without reading open sibling roots. -/
theorem negative_forest_own (valid : Guard → Prop) (depth : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (stored : MuStored valid before)
    (bounded : ∀ value ∈ values, Cap valid depth value) :
    Forest ((-1) :: path) values before .empty before ∧ MuStored valid before ∧ Cap valid 0 (.empty : Value Symbol Guard) ∧
      (∃ result after, Forest ((-1) :: path) values before result after ∧ SourceEqualityRequiredCache.Keeps before after ∧
        SemanticReady after ∧ Available after result ∧ result.free = [] ∧ MuStored valid after ∧
        Cap valid (depth - (((-1) :: path).length - 1)) result) := by
  have absent : select values (-1) = none := by simp [select]
  have domain : ForestClosed ((-1) :: path) values := by
    intro value found
    rw [absent] at found
    cases found
  exact ⟨.missing absent, stored, .plain 0 .empty,
    SourceCurrentConstrainedCapSelectedProjection.forest_complete valid depth ((-1) :: path) values before semantic
      available domain stored bounded⟩

#print axioms open_forest_own_endpoint
#check @open_forest_own_endpoint
#print axioms negative_forest_own
#check @negative_forest_own
end MicroCFTA.SelectedCapProjectionIntegration
