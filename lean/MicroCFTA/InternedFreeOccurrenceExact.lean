import MicroCFTA.InternedFreeOccurrenceNormalization

/-!
# Exact occurrence profiles for source union construction

Normalization cannot add an occurrence cost. Together with retention of
live input occurrences, this gives the exact profile for every source
union branch and complete canonical cache hit.
-/
namespace MicroCFTA.InternedFreeOccurrenceExact
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency InternedLiveEdges
open InternedNormalizationFree InternedFreeOccurrenceRank InternedFreeOccurrenceNormalization
open InternedBinderProtocol (Reference NodeKey)

/-- Concatenating ordinary edge lists concatenates their actual occurrence lists. -/
theorem edgeCosts_append (first second : List (EdgeValue Symbol Guard)) :
    edgeCosts (first ++ second) = edgeCosts first ++ edgeCosts second := by
  induction first with
  | nil => simp [edgeCosts]
  | cons head tail ih => cases head; simp [edgeCosts, ih, List.append_assoc]

/-- The source all-ordinary merge preserves the ordered pre-normalization occurrence list. -/
theorem ordinaryEdges_costs (values : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (found : ordinaryEdges values = some edges) : edgeCosts edges = manyCosts values := by
  induction values generalizing edges with
  | nil => cases found; simp [edgeCosts, manyCosts]
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at found <;> try contradiction
      case node entry own depth free =>
        cases tail : ordinaryEdges rest with
        | none => simp [tail] at found
        | some later =>
            have same : own ++ later = edges := by simpa [tail] using found
            subst edges
            simp only [edgeCosts_append, manyCosts, costs, ih later tail]

/-- Every surviving ordinary output occurrence came from an actual requested edge child. -/
theorem makeNode_cost_origin [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (item : Reference × Nat)
    (occurrence : item ∈ costs (run (makeNode edges) state).1) : item ∈ edgeCosts edges := by
  rw [makeNode_costs edges state coherent linked resident, edge_member] at occurrence
  obtain ⟨edge, selected, child, member, present⟩ := occurrence
  exact (edge_member edges item).mpr ⟨edge, (List.mem_filter.mp (canonicalEdges_member _ edge selected)).1, child, member, present⟩

/-- Complete canonical union readback contains the exact requested member occurrence list. -/
theorem union_readback_costs (state : State Symbol Guard) (coherent : Coherent state)
    (members : List (Value Symbol Guard)) (entry : Interned NodeKey) (result : Value Symbol Guard)
    (fields : NodeFields (.union (members.map Value.referenceOf)) entry result)
    (available : Available state result) (inputs : ∀ value ∈ members, Available state value) :
    costs result = manyCosts members := by
  cases result with
  | empty | reference | node | mu => simp [NodeFields, muKey] at fields
  | union actual originals depth free =>
      have same := value_lists_equal state coherent members originals
        (fun value member => (inputs value member).resident)
        (fun value member => (available.children value member).resident) (NodeKey.union.inj fields.2.1)
      simp only [costs, same]

/-- Actual union normalization introduces no free-reference occurrence or new binder cost. -/
theorem makeUnion_cost_origin [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state) (linked : Linked state)
    (available : ∀ value ∈ values, Available state value) (item : Reference × Nat)
    (occurrence : item ∈ costs (run (makeUnion values) state).1) :
    ∃ value ∈ values, item ∈ costs value := by
  have allAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value := by
    intro value member
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact unionMembers_available original (available original included) value selected
  have origin : ∀ value ∈ distinctNodes (values.flatMap unionMembers), item ∈ costs value →
      ∃ source ∈ values, item ∈ costs source := by
    intro value member present
    obtain ⟨source, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact ⟨source, included, (flatten_cost source item).mpr ⟨value, inner, present⟩⟩
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, normalized, run, costs] at occurrence
  | cons first rest =>
      cases rest with
      | nil => exact origin first (by simp [normalized]) (by simpa only [makeUnion, normalized, run] using occurrence)
      | cons second tail =>
          have memberAvailable : ∀ value ∈ first :: second :: tail, Available state value := by simpa [normalized] using allAvailable
          have fromMember : ∀ value ∈ first :: second :: tail, item ∈ costs value → ∃ source ∈ values, item ∈ costs source :=
            fun value member => origin value (by simpa [normalized] using member)
          cases ordinaryResult : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have resident := ordinaryEdges_resident _ edges state linked (fun value member => (memberAvailable value member).resident) ordinaryResult
              have inputCost := makeNode_cost_origin edges state coherent linked resident item
                (by simpa only [makeUnion, normalized, ordinaryResult] using occurrence)
              rw [ordinaryEdges_costs _ edges ordinaryResult, many_member] at inputCost
              obtain ⟨value, member, present⟩ := inputCost
              exact fromMember value member present
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
                intro value member
                simpa only [makeUnion, normalized, ordinaryResult, run] using
                  available_after_run (makeUnion values) state coherent.valid (memberAvailable value member)
              obtain ⟨actual, fields⟩ := InternedGateRank.requested_fields key identify state coherent
                (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              have same := union_readback_costs after afterCoherent members actual result fields output inputs
              simp only [makeUnion, normalized, ordinaryResult, run] at occurrence
              change item ∈ costs result at occurrence
              rw [same, many_member] at occurrence
              obtain ⟨value, member, present⟩ := occurrence
              exact fromMember value member present

/-- Every live source union output has exactly its original operand occurrence costs. -/
theorem makeUnion_cost_iff [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (available : ∀ value ∈ values, Available state value) (item : Reference × Nat) :
    item ∈ costs (run (makeUnion values) state).1 ↔ ∃ value ∈ values, item ∈ costs value :=
  ⟨makeUnion_cost_origin values state coherent cached linked available item,
    fun ⟨value, member, present⟩ => makeUnion_cost values state coherent cached linked live available value member item present⟩

end MicroCFTA.InternedFreeOccurrenceExact
