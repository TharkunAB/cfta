import MicroCFTA.InternedUnionNonemptyMembers
import MicroCFTA.InternedEmptyNormalization

/-!
# Root self-reference filtering preserves source emptiness

Every stored union has at least two distinct nonempty members. Removing
one literal self reference therefore leaves a nonempty operand. The actual
source filter changes no record's empty or nonempty status.
-/
namespace MicroCFTA.InternedFilterEmptiness
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedEdgeResidency InternedLiveEdges InternedNonemptyRecords InternedEmptyNormalization
open InternedUnionNonemptyMembers
open InternedBinderProtocol (Reference NodeRef NodeKey)

/-- A proper stored union retains a member different from any one specified reference. -/
theorem other_member (name : Reference) (entry : Interned NodeKey) (members : List (Value Symbol Guard))
    (depth : Nat) (free : List Reference) (proper : StoredNonempty (.union entry members depth free)) :
    ∃ value ∈ members, value.referenceOf ≠ .ref name := by
  cases members with
  | nil => simp [StoredNonempty] at proper
  | cons first rest =>
      cases rest with
      | nil => simp [StoredNonempty] at proper
      | cons second tail =>
          have distinct : first.referenceOf ≠ second.referenceOf := by
            have absent := (List.nodup_cons.mp proper.2).1
            intro same
            exact absent (by simp [same])
          by_cases same : first.referenceOf = .ref name
          · exact ⟨second, by simp, fun other => distinct (same.trans other.symm)⟩
          · exact ⟨first, by simp, same⟩

/-- Root self filtering preserves nonemptiness for every actual available record. -/
theorem filter_nonempty [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state) (live : Live state)
    (proper : NonemptyRecords state) (members : MembersNonempty state) (available : Available state value)
    (nonempty : value.referenceOf ≠ .empty) : (run (withoutSelfReference name value) state).1.referenceOf ≠ .empty := by
  cases value <;> simp only [withoutSelfReference, run] <;> try exact nonempty
  case union entry values depth free =>
    split
    · obtain ⟨chosen, member, different⟩ := other_member name entry values depth free
        (resident_nonempty state proper _ available.resident)
      have alive : chosen.referenceOf ≠ .empty := resident_membersNonempty state members _ available.resident chosen member
      exact InternedEmptyNormalization.makeUnion_nonempty _ state coherent linked live proper
        (fun value included => available.children value (List.mem_filter.mp included).1) chosen
        (List.mem_filter.mpr ⟨member, by simpa using different⟩) alive
    · exact nonempty

/-- The normalized source callback filter has exactly the original empty status. -/
theorem filter_empty_iff [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state) (live : Live state)
    (proper : NonemptyRecords state) (members : MembersNonempty state) (available : Available state value) :
    (run (withoutSelfReference name value) state).1.referenceOf = .empty ↔ value.referenceOf = .empty := by
  constructor
  · intro result
    by_cases original : value.referenceOf = .empty
    · exact original
    · exact False.elim (filter_nonempty name value state coherent linked live proper members available original result)
  · intro original
    have same := (reference_empty value).mp original
    subst value
    rfl

end MicroCFTA.InternedFilterEmptiness
