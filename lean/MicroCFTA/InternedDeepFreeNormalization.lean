import MicroCFTA.InternedDeepFreeDepth

/-!
# Deep references through actual source normalization

Union flattening and canonical readback preserve deep-name membership.
The all-ordinary branch combines complete edge payloads. Removing a bare
root reference therefore leaves all deep occurrences unchanged.
-/
namespace MicroCFTA.InternedDeepFreeNormalization
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedDeepFreeDepth InternedNormalizationFree InternedUnionSeparation InternedUnionDescendants
open InternedEdgeResidency InternedLiveEdges InternedStoredMuOrigins InternedUnionRetention
open InternedBinderProtocol (Reference NodeKey)

/-- Flattening a root union preserves every deep occurrence. -/
theorem flatten_deep (value : Value Symbol Guard) (name : Reference) :
    name ∈ deepNames value ↔ ∃ child ∈ unionMembers value, name ∈ deepNames child := by
  cases value <;> simp only [unionMembers, deepNames]
  · simp
  · simp [deepNames]
  · simp [deepNames]
  · exact deepMany_member _ name
  · simp [deepNames]

/-- Deep occurrences are also free occurrences in the complete source record. -/
theorem deep_free (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (name : Reference) (member : name ∈ deepNames value) : name ∈ value.free := by
  cases value with
  | empty | reference => simp [deepNames] at member
  | node | mu => simpa only [deepNames] using member
  | union entry members depth free =>
      obtain ⟨child, included, named⟩ := (deepMany_member members name).mp (by simpa only [deepNames] using member)
      rw [Value.free, union_free state coherent entry members depth free available.resident, childFree_member]
      exact ⟨child, included, deep_free child state coherent (available.children child included) name named⟩
termination_by sizeOf value
decreasing_by
  have smaller := List.sizeOf_lt_of_mem included
  simp_all only [Value.union.sizeOf_spec]
  omega

/-- Identity deduplication keeps exactly the deep names of available operands. -/
theorem normalized_deep (state : State Symbol Guard) (coherent : Coherent state)
    (values : List (Value Symbol Guard)) (available : ∀ value ∈ values, Available state value) (name : Reference) :
    (∃ value ∈ distinctNodes (values.flatMap unionMembers), name ∈ deepNames value) ↔
      ∃ value ∈ values, name ∈ deepNames value := by
  have allAvailable : ∀ value ∈ values.flatMap unionMembers, Available state value := by
    intro value member
    obtain ⟨outer, included, inner⟩ := List.mem_flatMap.mp member
    exact unionMembers_available outer (available outer included) value inner
  constructor
  · rintro ⟨value, member, deep⟩
    obtain ⟨outer, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact ⟨outer, included, (flatten_deep outer name).mpr ⟨value, inner, deep⟩⟩
  · rintro ⟨outer, included, deep⟩
    obtain ⟨value, inner, named⟩ := (flatten_deep outer name).mp deep
    exact ⟨value, distinctNodes_retains state coherent _
      (fun value member => (allAvailable value member).resident) value (List.mem_flatMap.mpr ⟨outer, included, inner⟩), named⟩

/-- Ordinary readback places every free name below its ordinary boundary. -/
theorem makeNode_deep [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    deepNames (run (makeNode edges) state).1 = (run (makeNode edges) state).1.free := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · simp [run, deepNames, Value.free]
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa [same] using selected)
    simp only [run, exactResult, identifyNode, deepNames]

/-- A complete union readback retains the exact requested deep occurrences. -/
theorem union_readback_deep (state : State Symbol Guard) (coherent : Coherent state)
    (members : List (Value Symbol Guard)) (entry : Interned NodeKey) (result : Value Symbol Guard)
    (fields : NodeFields (.union (members.map Value.referenceOf)) entry result)
    (output : Available state result) (inputs : ∀ value ∈ members, Available state value)
    (name : Reference) : name ∈ deepNames result ↔ ∃ value ∈ members, name ∈ deepNames value := by
  cases result with
  | empty | reference | node | mu => simp [NodeFields, muKey] at fields
  | union actual own depth free =>
      have equal := value_lists_equal state coherent members own
        (fun value member => (inputs value member).resident)
        (fun value member => (output.children value member).resident)
        (NodeKey.union.inj fields.2.1)
      simpa only [deepNames, ← equal] using deepMany_member members name

/-- All source union branches preserve exactly the deep names of their operands. -/
theorem makeUnion_deep [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state)
    (available : ∀ value ∈ values, Available state value) (name : Reference) :
    name ∈ deepNames (run (makeUnion values) state).1 ↔ ∃ value ∈ values, name ∈ deepNames value := by
  have allAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value := by
    intro value member
    obtain ⟨outer, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact unionMembers_available outer (available outer included) value inner
  have built := makeUnion_available values state coherent cached available
  rw [← normalized_deep state coherent values available name]
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, normalized, run, deepNames]
  | cons first rest =>
      cases rest with
      | nil => simp [makeUnion, normalized, run]
      | cons second tail =>
          have memberAvailable : ∀ value ∈ first :: second :: tail, Available state value := by simpa [normalized] using allAvailable
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have resident := ordinaryEdges_resident _ edges state linked
                (fun value member => (memberAvailable value member).resident) ordinary
              have deepSame : ∀ value ∈ first :: second :: tail, deepNames value = value.free := by
                intro value member
                obtain ⟨entry, own, depth, free, rfl, _⟩ := ordinaryEdges_contains _ edges ordinary value member
                simp only [deepNames]
              have free := (makeUnion_free values state coherent cached linked live available name).trans
                (normalized_free state coherent values available name).symm
              simp only [makeUnion, normalized, ordinary]
              change name ∈ deepNames (run (makeNode edges) state).1 ↔ _
              rw [makeNode_deep edges state coherent linked resident]
              have freeResult : name ∈ (run (makeNode edges) state).1.free ↔
                  ∃ value ∈ first :: second :: tail, name ∈ value.free := by
                simpa only [makeUnion, normalized, ordinary] using free
              apply freeResult.trans
              apply exists_congr
              intro value
              apply and_congr_right
              intro member
              rw [deepSame value member]
          | none =>
              let members := first :: second :: tail
              let key := NodeKey.union (members.map Value.referenceOf)
              let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
              let after := (nodeStep key identify state).2
              let result := (nodeStep key identify state).1
              have output : Available after result := by simpa only [makeUnion, normalized, ordinary, run] using built.2.2
              have later : Coherent after := by simpa only [makeUnion, normalized, ordinary, run] using built.1
              have inputs : ∀ value ∈ members, Available after value := by
                intro value member
                simpa only [makeUnion, normalized, ordinary, run] using
                  available_after_run (makeUnion values) state coherent.valid (memberAvailable value member)
              obtain ⟨actual, fields⟩ := InternedGateRank.requested_fields key identify state coherent
                (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              have readback := union_readback_deep after later members actual result fields output inputs name
              simpa only [makeUnion, normalized, ordinary, run] using readback

/-- Root self filtering removes no deep occurrence of any reference. -/
theorem filter_deep [DecidableEq (EdgeKey Symbol Guard)] (localName name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state value) :
    name ∈ deepNames (run (withoutSelfReference localName value) state).1 ↔ name ∈ deepNames value := by
  cases value <;> simp only [withoutSelfReference, run] <;> try exact Iff.rfl
  case union entry members depth free =>
    split
    · rw [makeUnion_deep (members.filter (fun member => member.referenceOf != .ref localName)) state
        normal.facts.coherent normal.facts.cached normal.facts.linked normal.live
        (fun value member => available.children value (List.mem_filter.mp member).1) name,
        deepNames, deepMany_member]
      constructor
      · rintro ⟨child, included, named⟩
        exact ⟨child, (List.mem_filter.mp included).1, named⟩
      · rintro ⟨child, included, named⟩
        refine ⟨child, (withoutSelfReference_members localName members child).mpr ⟨included, ?_⟩, named⟩
        intro same
        simp [same, deepNames] at named
    · exact Iff.rfl

end MicroCFTA.InternedDeepFreeNormalization
