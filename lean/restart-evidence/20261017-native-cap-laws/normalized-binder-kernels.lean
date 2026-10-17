import MicroCFTA.SourceCurrentConstrainedCapNormalizedBinder

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.NormalizedBinderKernels
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance
open InternedNestedConstruction (Outcome work)
open InternedBinderProtocol (Reference NodeKey)
local notation "Heap" => InternedConstructorTemplates.State Nat Bool
local notation "V" => Value Nat Bool
local notation "P" => fun guard : Bool => guard = true
private def edge := run (makeEdge 7 false []) (empty : Heap)
private def ordinary := run (makeNode [edge.1]) edge.2
private def old := Reference.intersection 0 1
private def direct := run (makeUnion [.reference old, ordinary.1]) ordinary.2

private theorem ordinary_value : ordinary.1 = .node ⟨0, .node [0]⟩ [.mk ⟨0, ⟨7, [], false⟩⟩ []] 0 [] := by
  simp [ordinary, edge, run, makeNode, makeEdge, canonicalEdges, surviving,
    EnumerationBuilderCaches.canonicalIds, List.eraseDups_cons, nodeStep, edgeStep, identifyNode,
    maximumDepth, childFree, canonicalFree, EdgeValue.children, EdgeValue.entry, empty,
    Cache.intern, Cache.emptyState, Cache.reserve, Cache.install, Cache.keepFirst, Cache.put]

/-- Actual edge, node, and union construction produce a nonhereditary cap input and its own finite optional binder. -/
theorem constructed_nonplain_then_replay :
    ∃ final,
      SourceRecursiveIntersectionMaybeMu.maybeMu (0, 1) direct.1 direct.2 = .done ordinary.1 final ∧
      Facts final ∧ Available final ordinary.1 ∧
      SourceCurrentConstrainedCap.Cap P 1 ordinary.1 ∧
      ¬ SourceEqualityAnnotationLanguage.Annotated P ordinary.1 ∧
      ∀ later, Grows final later →
        SourceRecursiveIntersectionMaybeMu.maybeMu (0, 1) direct.1 later = .done ordinary.1 later := by
  have edgeChecked := edge_verified 7 false [] (empty : Heap) empty_facts (by intro value member; cases member)
  have nodeChecked := node_verified [edge.1] edge.2 edgeChecked.facts (by
    intro value member
    exact List.mem_singleton.mp member ▸ edgeChecked.result edge.1 edge.2 rfl)
  have facts : Facts ordinary.2 := nodeChecked.facts
  have available : Available ordinary.2 ordinary.1 := nodeChecked.result ordinary.1 ordinary.2 rfl
  have reference : Available ordinary.2 (.reference old) := reference_available _ _ (by
    intro identity member
    simp [old, Value.free] at member)
  have inputs : Values ordinary.2 [.reference old, ordinary.1] := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact reference
    · exact List.mem_singleton.mp member ▸ available
  have built := union_verified [.reference old, ordinary.1] ordinary.2 facts inputs
  have bodyFacts : Facts direct.2 := built.facts
  have bodyAvailable : Available direct.2 direct.1 := built.result direct.1 direct.2 rfl
  have selected : distinctNodes (([.reference old, ordinary.1] : List V).flatMap unionMembers) =
      [.reference old, ordinary.1] := by rw [ordinary_value]; simp [unionMembers, distinctNodes, Value.referenceOf]
  obtain ⟨entry, actualBody⟩ := InternedUnionFilterFusion.union_readback [.reference old, ordinary.1]
    (.reference old) ordinary.1 [] ordinary.2 facts inputs selected rfl
  have same : direct.1 = SourceCurrentConstrainedCapNormalizedBinder.body old entry ⟨0, .node [0]⟩
      [.mk ⟨0, ⟨7, [], false⟩⟩ []] 0 0 := by
    simpa [direct, ordinary_value, maximumDepth, childFree, Value.depth, Value.free, canonicalFree,
      List.eraseDups_cons, SourceCurrentConstrainedCapNormalizedBinder.body] using actualBody
  have cap : SourceCurrentConstrainedCap.Cap P 1 ordinary.1 := by
    rw [ordinary_value]
    apply SourceCurrentConstrainedCap.Cap.node 0
    intro value member
    simp [EdgeValue.children] at member
  have nonplain : ¬SourceEqualityAnnotationLanguage.Annotated P ordinary.1 := by
    rw [ordinary_value]
    intro annotated
    cases annotated with
    | node entry edges level free guards children =>
        have impossible := guards (.mk ⟨0, ⟨7, [], false⟩⟩ []) (by simp)
        change false = true at impossible
        cases impossible
  have fresh : direct.2.nodes.table (muKey ordinary.1 ordinary.1) = none := by decide +kernel
  rw [same] at bodyAvailable
  rw [ordinary_value] at cap fresh
  obtain ⟨final, done, finalFacts, _growth, _history, finalAvailable, resultCap, replay⟩ :=
    SourceCurrentConstrainedCapNormalizedBinder.complete_replay P 1 (0, 1) entry ⟨0, .node [0]⟩
      [.mk ⟨0, ⟨7, [], false⟩⟩ []] 0 0 direct.2 bodyFacts bodyAvailable cap fresh
  refine ⟨final, ?_, finalFacts, ?_, ?_, nonplain, ?_⟩
  · rw [same]
    simpa only [old, ← ordinary_value] using done
  · simpa only [← ordinary_value] using finalAvailable
  · simpa only [← ordinary_value] using resultCap
  · intro later growth
    rw [same]
    simpa only [old, ← ordinary_value] using replay later growth

#print axioms constructed_nonplain_then_replay
#check @constructed_nonplain_then_replay
end MicroCFTA.NormalizedBinderKernels
