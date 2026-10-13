import MicroCFTA.InternedFilterSelfReference
import MicroCFTA.InternedUnionSeparation

/-!
# Exact literal-reference results of source union construction

A source union returns a literal reference exactly when at least one input
is that reference and every input is empty or that reference. Stored union
records cannot hide another case because they have two distinct members.
-/
namespace MicroCFTA.InternedUnionReference
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNonemptyRecords InternedFilterSelfReference InternedUnionSeparation
open InternedGateRank InternedNestedFacts InternedNestedProvenance
open InternedBinderProtocol (Reference NodeKey)

/-- A literal result selects exactly the singleton branch of source union normalization. -/
theorem normalized_singleton_iff [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state) :
    (run (makeUnion values) state).1 = .reference name ↔
      distinctNodes (values.flatMap unionMembers) = [.reference name] := by
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, normalized, run]
  | cons first rest =>
      cases rest with
      | nil => simp [makeUnion, normalized, run]
      | cons second tail =>
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              simp only [makeUnion, normalized, ordinary, List.cons.injEq, reduceCtorEq, and_false, iff_false]
              exact makeNode_not_reference name edges state coherent
          | none =>
              simp only [makeUnion, normalized, ordinary, run, List.cons.injEq, reduceCtorEq, and_false, iff_false]
              obtain ⟨entry, fields⟩ := requested_fields
                (.union ((first :: second :: tail).map Value.referenceOf))
                (fun entry => .union entry (first :: second :: tail)
                  (maximumDepth (first :: second :: tail)) (childFree (first :: second :: tail)))
                state coherent (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              intro same
              rw [same] at fields
              exact fields

/-- An available operand whose flattened members are all one reference is empty or that reference. -/
theorem operand_cases (name : Reference) (value : Value Symbol Guard) (state : State Symbol Guard)
    (proper : NonemptyRecords state) (available : Available state value)
    (only : ∀ member ∈ unionMembers value, member.referenceOf = .ref name) :
    value = .empty ∨ value = .reference name := by
  cases value with
  | empty => exact Or.inl rfl
  | reference other =>
      right
      exact (referenceOf_self_iff name (.reference other)).mp (only _ (by simp [unionMembers]))
  | node entry edges depth free =>
      have impossible := only (.node entry edges depth free) (by simp [unionMembers])
      cases impossible
  | mu entry body depth ordinary =>
      have impossible := only (.mu entry body depth ordinary) (by simp [unionMembers])
      cases impossible
  | union entry members depth free =>
      obtain ⟨length, unique⟩ := resident_nonempty state proper (.union entry members depth free) available.resident
      cases members with
      | nil => simp at length
      | cons first rest =>
          cases rest with
          | nil => simp at length
          | cons second tail =>
              have firstSame := only first (by simp [unionMembers])
              have secondSame := only second (by simp [unionMembers])
              have apart := (List.nodup_cons.mp unique).1
              exact False.elim (apart (by simp [firstSame, secondSame]))

/-- A nonempty list of copies of one bare reference normalizes to that reference. -/
theorem distinct_reference (name : Reference) (values : List (Value Symbol Guard))
    (present : .reference name ∈ values) (only : ∀ value ∈ values, value = .reference name) :
    distinctNodes values = [.reference name] := by
  cases values with
  | nil => simp at present
  | cons first rest =>
      have same := only first List.mem_cons_self
      subst first
      have erased : rest.filter (fun other => other.referenceOf != (.reference name : Value Symbol Guard).referenceOf) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro value member
        simp [only value (List.mem_cons_of_mem _ member), Value.referenceOf]
      simp [distinctNodes, erased]

/-- The actual union returns a bare reference exactly for nonempty empty-or-self source inputs. -/
theorem makeUnion_reference_iff [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (proper : NonemptyRecords state) (inputs : Values state values) :
    (run (makeUnion values) state).1 = .reference name ↔
      .reference name ∈ values ∧ ∀ value ∈ values, value = .empty ∨ value = .reference name := by
  rw [normalized_singleton_iff name values state coherent]
  constructor
  · intro singleton
    have only : ∀ value ∈ values, value = .empty ∨ value = .reference name := by
      intro value member
      apply operand_cases name value state proper (inputs value member)
      intro inner included
      exact singleton_all _ (.reference name) singleton inner (List.mem_flatMap.mpr ⟨value, member, included⟩)
    have selected := distinctNodes_member (values.flatMap unionMembers) (.reference name) (by simp [singleton])
    obtain ⟨value, member, included⟩ := List.mem_flatMap.mp selected
    rcases only value member with rfl | rfl
    · simp [unionMembers] at included
    · exact ⟨member, only⟩
  · rintro ⟨present, only⟩
    apply distinct_reference name
    · exact List.mem_flatMap.mpr ⟨.reference name, present, by simp [unionMembers]⟩
    · intro inner included
      obtain ⟨value, member, selected⟩ := List.mem_flatMap.mp included
      rcases only value member with rfl | rfl
      · simp [unionMembers] at selected
      · simpa [unionMembers] using selected

end MicroCFTA.InternedUnionReference
