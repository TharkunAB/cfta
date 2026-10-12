import MicroCFTA.InternedFreeOccurrenceRank

/-!
# Free-occurrence costs through actual source normalization

Canonical readback retains complete child records. Ordinary node
normalization retains each live edge occurrence. Every union branch then
retains each operand's occurrence cost, including singleton collapse.
-/
namespace MicroCFTA.InternedFreeOccurrenceNormalization
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency InternedLiveEdges
open InternedUnionRetention InternedUnionDescendants InternedNormalizationFree InternedFreeOccurrenceRank
open InternedBinderProtocol (Reference NodeKey)

/-- An ordered child occurrence keeps its original cost. -/
theorem many_member (values : List (Value Symbol Guard)) (item : Reference × Nat) :
    item ∈ manyCosts values ↔ ∃ value ∈ values, item ∈ costs value := by
  induction values with
  | nil => simp [manyCosts]
  | cons first rest ih => simp [manyCosts, ih]

/-- An edge occurrence comes from one of its complete ordered child records. -/
theorem edge_member (edges : List (EdgeValue Symbol Guard)) (item : Reference × Nat) :
    item ∈ edgeCosts edges ↔ ∃ edge ∈ edges, ∃ child ∈ edge.children, item ∈ costs child := by
  induction edges with
  | nil => simp [edgeCosts]
  | cons first rest ih =>
      cases first with
      | mk entry children => simp [edgeCosts, many_member, ih, EdgeValue.children]

/-- Root union flattening preserves every occurrence with its exact binder cost. -/
theorem flatten_cost (value : Value Symbol Guard) (item : Reference × Nat) :
    item ∈ costs value ↔ ∃ member ∈ unionMembers value, item ∈ costs member := by
  cases value with
  | empty => simp [costs, unionMembers]
  | union => simpa only [costs, unionMembers] using many_member _ item
  | reference | node | mu => simp [unionMembers]

/-- Actual ordinary cache readback retains the exact surviving occurrence list. -/
theorem makeNode_costs [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    costs (run (makeNode edges) state).1 = edgeCosts (canonicalEdges (surviving edges)) := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · rename_i same
    simp [run, costs, same, edgeCosts]
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state coherent linked (by simpa [same] using selected)
    simp only [run, readback, identifyNode, costs, same]

/-- Sorting, deduplication, and actual canonical readback retain a live edge's original occurrence cost. -/
theorem makeNode_cost [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (edge : EdgeValue Symbol Guard) (present : edge ∈ edges)
    (live : edge.children.any (fun child => child.referenceOf == .empty) = false)
    (child : Value Symbol Guard) (member : child ∈ edge.children) (item : Reference × Nat)
    (occurrence : item ∈ costs child) : item ∈ costs (run (makeNode edges) state).1 := by
  rw [makeNode_costs edges state coherent linked resident, edge_member]
  have survives : edge ∈ surviving edges := by simp [surviving, present, live]
  exact ⟨edge, canonicalEdges_retains state coherent _ edge
    (fun value included => resident value (List.mem_filter.mp included).1) survives, child, member, occurrence⟩

/-- Complete interned-union readback retains the actual requested members and their costs. -/
theorem union_readback_cost (state : State Symbol Guard) (coherent : Coherent state)
    (members : List (Value Symbol Guard)) (entry : Interned NodeKey) (result : Value Symbol Guard)
    (fields : NodeFields (.union (members.map Value.referenceOf)) entry result)
    (available : Available state result) (inputs : ∀ value ∈ members, Available state value)
    (source : Value Symbol Guard) (member : source ∈ members) (item : Reference × Nat)
    (occurrence : item ∈ costs source) : item ∈ costs result := by
  cases result with
  | empty | reference | node | mu => simp [NodeFields, muKey] at fields
  | union actual originals depth free =>
      have ids := NodeKey.union.inj fields.2.1
      have same := value_lists_equal state coherent members originals
        (fun value member => (inputs value member).resident)
        (fun value member => (available.children value member).resident) ids
      simp only [costs, ← same, many_member]
      exact ⟨source, member, occurrence⟩

/-- Every actual union branch retains each source occurrence at exactly the same binder cost. -/
theorem makeUnion_cost [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (available : ∀ value ∈ values, Available state value)
    (source : Value Symbol Guard) (member : source ∈ values) (item : Reference × Nat)
    (occurrence : item ∈ costs source) : item ∈ costs (run (makeUnion values) state).1 := by
  obtain ⟨source, inner, occurrence⟩ := (flatten_cost source item).mp occurrence
  have allAvailable : ∀ value ∈ values.flatMap unionMembers, Available state value := by
    intro value present
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp present
    exact unionMembers_available original (available original included) value selected
  have flattened : source ∈ values.flatMap unionMembers := List.mem_flatMap.mpr ⟨_, member, inner⟩
  have sourceAvailable := allAvailable source flattened
  have selected := distinctNodes_retains state coherent _ (fun value member => (allAvailable value member).resident) source flattened
  have normalizedAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value :=
    fun value member => allAvailable value (distinctNodes_member _ value member)
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [normalized] at selected
  | cons first rest =>
      cases rest with
      | nil =>
          have same : source = first := by simpa [normalized] using selected
          simpa only [makeUnion, normalized, run, ← same] using occurrence
      | cons second tail =>
          have sourceMember : source ∈ first :: second :: tail := by simpa [normalized] using selected
          have memberAvailable : ∀ value ∈ first :: second :: tail, Available state value := by simpa [normalized] using normalizedAvailable
          cases ordinaryResult : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              obtain ⟨sourceEntry, sourceEdges, sourceDepth, sourceFree, same, included⟩ :=
                ordinaryEdges_contains _ edges ordinaryResult source sourceMember
              subst source
              obtain ⟨edge, present, child, childMember, childCost⟩ := (edge_member sourceEdges item).mp (by simpa only [costs] using occurrence)
              have resident := ordinaryEdges_resident _ edges state linked
                (fun value member => (memberAvailable value member).resident) ordinaryResult
              have edgeLive := resident_live state live _ sourceAvailable.resident edge present
              simpa only [makeUnion, normalized, ordinaryResult] using
                makeNode_cost edges state coherent linked resident edge (included edge present) edgeLive child childMember item childCost
          | none =>
              let members := first :: second :: tail
              let key := NodeKey.union (members.map Value.referenceOf)
              let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
              let after := (nodeStep key identify state).2
              let result := (nodeStep key identify state).1
              have built := makeUnion_available values state coherent cached available
              have output : Available after result := by simpa only [makeUnion, normalized, ordinaryResult, run] using built.2.2
              have afterCoherent : Coherent after := by simpa only [makeUnion, normalized, ordinaryResult, run] using built.1
              have inputs : ∀ value ∈ members, Available after value := by
                intro value present
                simpa only [makeUnion, normalized, ordinaryResult, run] using
                  available_after_run (makeUnion values) state coherent.valid (memberAvailable value present)
              obtain ⟨actual, fields⟩ := InternedGateRank.requested_fields key identify state coherent
                (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              simpa only [makeUnion, normalized, ordinaryResult, run] using
                union_readback_cost after afterCoherent members actual result fields output inputs source sourceMember item occurrence

/-- Source root self-reference filtering preserves every other free occurrence and its cost. -/
theorem filter_cost_other [DecidableEq (EdgeKey Symbol Guard)] (name other : Reference)
    (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (available : Available state value)
    (different : other ≠ name) (count : Nat) (occurrence : (other, count) ∈ costs value) :
    (other, count) ∈ costs (run (withoutSelfReference name value) state).1 := by
  cases value <;> simp only [withoutSelfReference, run] <;> try exact occurrence
  case union entry members depth free =>
    split
    · obtain ⟨source, member, present⟩ := (many_member members (other, count)).mp (by simpa only [costs] using occurrence)
      apply makeUnion_cost _ state coherent cached linked live
        (fun value included => available.children value (List.mem_filter.mp included).1) source _ (other, count) present
      apply (withoutSelfReference_members name members source).mpr
      refine ⟨member, ?_⟩
      intro same
      subst source
      simp [costs, different] at present
    · exact occurrence

/-- An actual occurrence bounds the executable minimum, independently of cached metadata. -/
theorem rank_le_cost (value : Value Symbol Guard) (name : Reference) (count : Nat)
    (occurrence : (name, count) ∈ costs value) : rank value ≤ count := by
  have member : count ∈ (costs value).map Prod.snd := List.mem_map.mpr ⟨(name, count), occurrence, rfl⟩
  cases least : ((costs value).map Prod.snd).min? with
  | none =>
      have empty := List.min?_eq_none_iff.mp least
      simp [empty] at member
  | some minimum =>
      simpa only [rank, least, Option.getD_some] using (List.min?_eq_some_iff.mp least).2 count member

/-- Smart cleanup retains each free occurrence with no greater binder cost. -/
theorem cleanup_cost (value : Value Symbol Guard) (name : Reference) (count : Nat)
    (occurrence : (name, count) ∈ costs value) :
    ∃ after ≤ count, (name, after) ∈ costs (cleanup value) := by
  cases value with
  | empty | reference | node | union => exact ⟨count, Nat.le_refl _, occurrence⟩
  | mu entry body depth ordinary =>
      simp only [cleanup]
      split
      · obtain ⟨⟨actual, prior⟩, selected, equal⟩ := List.mem_map.mp (by simpa only [costs] using occurrence)
        have sameName := congrArg Prod.fst equal
        have sameCost := congrArg Prod.snd equal
        change actual = name at sameName
        change prior + 1 = count at sameCost
        subst actual
        exact ⟨prior, by omega, (List.mem_filter.mp selected).1⟩
      · split
        · rename_i bare
          cases body <;> simp only [Value.referenceOf] at bare <;> try contradiction
          case reference =>
            have same := InternedBinderProtocol.NodeRef.ref.inj bare
            rw [same] at occurrence
            simp [costs] at occurrence
        · exact ⟨count, Nat.le_refl _, occurrence⟩

/-- Smart cleanup cannot increase the free-occurrence rank of an actual open record. -/
theorem cleanup_rank (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (opened : value.free ≠ []) : rank (cleanup value) ≤ rank value := by
  obtain ⟨name, occurrence⟩ := (rank_spec value state coherent available opened).1
  obtain ⟨after, bound, present⟩ := cleanup_cost value name (rank value) occurrence
  exact Nat.le_trans (rank_le_cost (cleanup value) name after present) bound

/-- Every live source union result is bounded by each original available operand occurrence. -/
theorem makeUnion_rank_le [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (available : ∀ value ∈ values, Available state value)
    (source : Value Symbol Guard) (member : source ∈ values) (name : Reference) (count : Nat)
    (occurrence : (name, count) ∈ costs source) : rank (run (makeUnion values) state).1 ≤ count :=
  rank_le_cost _ name count (makeUnion_cost values state coherent cached linked live available source member (name, count) occurrence)

end MicroCFTA.InternedFreeOccurrenceNormalization
