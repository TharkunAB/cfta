import MicroCFTA.SourceCurrentConstrainedCapPairOccurrenceCallbacks

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.PairOccurrencesKernels
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedStoredMuOrigins
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapPairOccurrences (Classified FreeLE sourceWeight identityWeight)
open SourceCurrentConstrainedCapPairOccurrenceCallbacks (mark)
local notation "Heap" => InternedConstructorTemplates.State Nat Bool
local notation "V" => Value Nat Bool
local notation "P" => fun guard : Bool => guard = true
private def edge := run (makeEdge 7 false []) (empty : Heap)
private def ordinary := run (makeNode [edge.1]) edge.2
private def old := Reference.intersection 0 1
private def direct := run (makeUnion [.reference old, ordinary.1]) ordinary.2
private noncomputable def ownerBound := sourceWeight P direct.2 old

private theorem ordinary_value : ordinary.1 = .node ⟨0, .node [0]⟩ [.mk ⟨0, ⟨7, [], false⟩⟩ []] 0 [] := by
  simp [ordinary, edge, run, makeNode, makeEdge, canonicalEdges, surviving,
    EnumerationBuilderCaches.canonicalIds, List.eraseDups_cons, nodeStep, edgeStep, identifyNode,
    maximumDepth, childFree, canonicalFree, EdgeValue.children, EdgeValue.entry, empty,
    Cache.intern, Cache.emptyState, Cache.reserve, Cache.install, Cache.keepFirst, Cache.put]

open scoped Classical in
/-- An actual ordinary boundary consumes a smaller free-occurrence bound in each ordered child. -/
theorem actual_ordinary_from_smaller {Symbol Guard : Type}
    (weight : Reference → Nat) (smaller bound : Nat) (decrease : smaller < bound)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (resident : ∀ edge ∈ edges, InternedEdgeResidency.EdgeResident state edge)
    (children : ∀ edge ∈ edges, ∀ child ∈ edge.children, FreeLE weight smaller child)
    (owner : Reference) (maximal : bound ≤ weight owner) :
    let actual := run (makeNode edges) state
    Classified weight bound actual.1 ∧ owner ∉ InternedDeepFreeDepth.deepNames actual.1 := by
  have produced := SourceCurrentConstrainedCapPairOccurrences.makeNode weight bound edges state facts resident (by
    intro edge member child inside
    have lower := children edge member child inside
    exact ⟨fun name present => Nat.le_trans (lower name present) (Nat.le_of_lt decrease), lower.below decrease⟩)
  exact ⟨produced, produced.not_deep (by omega) owner maximal⟩

#print axioms actual_ordinary_from_smaller
#check @actual_ordinary_from_smaller

/-- Actual allocation, substitution, and normalization transport a positive local marker above a nonplain ordinary value. -/
theorem constructed_nonplain_marked_callback :
    0 < ownerBound ∧ ∃ (state : Heap) (owner : Interned NodeKey) (raw : V) (after : Heap),
      sourceWeight P direct.2 (.interned owner.identity) = 0 ∧
      mark (sourceWeight P direct.2) (.interned owner.identity) ownerBound (.interned owner.identity) = ownerBound ∧
      InternedFreshOrdinaryStoredSubstitution.execute direct.1
        (InternedStoredSubstitutionRebind.replacement old (.reference (.interned owner.identity))) state = .done raw after ∧
      Classified (mark (sourceWeight P direct.2) (.interned owner.identity) ownerBound) ownerBound raw ∧
      SourceRecursiveIntersectionMaybeMu.callback old direct.1 (.interned owner.identity) state = .done ordinary.1 after ∧
      InternedNestedConstruction.finish true (.mu owner ordinary.1 ordinary.1 ordinary.1) = ordinary.1 ∧
      SourceCurrentConstrainedCap.Cap P 1 ordinary.1 ∧
      ¬SourceEqualityAnnotationLanguage.Annotated P ordinary.1 := by
  have edgeChecked := edge_verified 7 false [] (empty : Heap) empty_facts (by intro value member; cases member)
  have nodeChecked := node_verified [edge.1] edge.2 edgeChecked.facts (by
    intro value member
    exact List.mem_singleton.mp member ▸ edgeChecked.result edge.1 edge.2 rfl)
  have normalOrdinary : Normal ordinary.2 := by
    have produced := InternedFreshOrdinaryNormal.build_normal
      (InternedNestedConstruction.Syntax.node [.mk 7 false []]) [] (empty : Heap) empty_normal
      (by intro value member; cases member)
    simpa [InternedFreshOrdinaryConstruction.build, InternedFreshOrdinaryConstruction.buildMany,
      InternedFreshOrdinaryConstruction.buildEdges, Outcome.bind, InternedNestedConstruction.work, Outcome.state, ordinary, edge] using produced
  have available : Available ordinary.2 ordinary.1 := nodeChecked.result ordinary.1 ordinary.2 rfl
  have oldAvailable : Available ordinary.2 (.reference old) := reference_available _ _ (by
    intro identity member
    simp [old, Value.free] at member)
  have inputs : Values ordinary.2 [.reference old, ordinary.1] := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact oldAvailable
    · exact List.mem_singleton.mp member ▸ available
  have built := union_verified [.reference old, ordinary.1] ordinary.2 nodeChecked.facts inputs
  have normalDirect : Normal direct.2 := by
    have produced := InternedFreshOrdinaryNormal.build_normal
      (InternedNestedConstruction.Syntax.union [.var 0, .var 1]) [.reference old, ordinary.1]
      ordinary.2 normalOrdinary inputs
    simpa [InternedFreshOrdinaryConstruction.build, InternedFreshOrdinaryConstruction.buildMany,
      Outcome.bind, InternedNestedConstruction.work, Outcome.state, direct] using produced
  have bodyAvailable : Available direct.2 direct.1 := built.result direct.1 direct.2 rfl
  have selected : distinctNodes (([.reference old, ordinary.1] : List V).flatMap unionMembers) =
      [.reference old, ordinary.1] := by rw [ordinary_value]; simp [unionMembers, distinctNodes, Value.referenceOf]
  obtain ⟨entry, actualBody⟩ := InternedUnionFilterFusion.union_readback [.reference old, ordinary.1]
    (.reference old) ordinary.1 [] ordinary.2 nodeChecked.facts inputs selected rfl
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
  have readFirst : SourcePreparedSharedRows.read direct.2 0 = some ordinary.1 :=
    SourcePreparedSharedRows.read_identity direct.2 built.facts ordinary.1 (built.available _ available) 0
      (by rw [ordinary_value]; rfl)
  have rankPositive := (SourceCurrentConstrainedCapNonplainRank.rank_pos_iff P ordinary.1).mpr nonplain
  have positive : 0 < ownerBound := by
    change 0 < identityWeight P direct.2 0 + identityWeight P direct.2 1
    have firstWeight : identityWeight P direct.2 0 = SourceCurrentConstrainedCapNonplainRank.rank P ordinary.1 := by
      simp only [identityWeight, readFirst, Option.map_some, Option.getD_some]
    rw [firstWeight]
    omega
  refine ⟨positive, ?_⟩
  let key := muKey ordinary.1 ordinary.1
  let allocated : Heap := {direct.2 with nodes := (Cache.intern direct.2.nodes key).2}
  let owner := (Cache.intern direct.2.nodes key).1
  have normalAllocated : Normal allocated := reserve_normal key direct.2 normalDirect
  have growth : Grows direct.2 allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have history := InternedFreshProbeKeys.intern_issued_extends direct.2.nodes key normalDirect.facts.coherent.valid.2
  have bodyAllocated := bodyAvailable.grows _ _ growth history
  have localAvailable : Available allocated (.reference (.interned owner.identity)) :=
    (InternedConstructionProvenance.reserve_available key direct.2 normalDirect.facts.coherent normalDirect.facts.cached).2
  rw [same] at bodyAllocated
  rw [ordinary_value] at cap
  have produced := SourceCurrentConstrainedCapPairOccurrenceCallbacks.callback
    (sourceWeight P direct.2) ownerBound P 1 old (.interned owner.identity) entry ⟨0, .node [0]⟩
    [.mk ⟨0, ⟨7, [], false⟩⟩ []] 0 0 allocated normalAllocated bodyAllocated localAvailable cap
  let raw := run (makeUnion [.reference (.interned owner.identity), ordinary.1]) allocated
  refine ⟨allocated, owner, raw.1, raw.2, rfl, by simp [mark], ?_, ?_, ?_, ?_, ?_, nonplain⟩
  · rw [same]
    simpa only [raw, ordinary_value] using produced.1
  · simpa only [raw, ordinary_value] using produced.2.1
  · rw [same]
    simpa only [raw, ordinary_value] using produced.2.2.1
  · rw [ordinary_value]
    simp [InternedNestedConstruction.finish, cleanup, Value.free]
  · simpa only [← ordinary_value] using cap

#print axioms constructed_nonplain_marked_callback
#check @constructed_nonplain_marked_callback
end MicroCFTA.PairOccurrencesKernels
