import MicroCFTA.InternedRootProfileNode
import MicroCFTA.InternedStoredMuOrigins

/-!
# Literal-reference reflection from source root profiles

Pure profiles contain exactly the actual free names. A singleton profile
is a bare reference for normalized available source records. Stored union
cardinality and distinct identities exclude a hidden singleton union.
-/
namespace MicroCFTA.InternedRootProfileReflection
open Cache InternedConstructorTemplates InternedRootProfile InternedRootProfileLists
open InternedRecordCoherence InternedProbeProvenance InternedStoredMuOrigins
open InternedNormalizationFree InternedUnionNormalForm InternedNonemptyRecords InternedUnionNonemptyMembers
open InternedBinderProtocol (Reference)

/-- Every member of a pure combined profile also has a pure profile. -/
theorem member_pure (values : List (Value Symbol Guard)) (names : List Reference) (pure : many values = some names)
    (value : Value Symbol Guard) (member : value ∈ values) : ∃ refs, profile value = some refs := by
  cases found : profile value with
  | some refs => exact ⟨refs, rfl⟩
  | none =>
      have impossible := (many_none_iff values).mpr ⟨value, member, found⟩
      simp [pure] at impossible

/-- In a pure source profile, reference membership is exactly actual free-name membership. -/
theorem pure_free (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (names : List Reference) (pure : profile value = some names) (name : Reference) :
    name ∈ value.free ↔ name ∈ names := by
  cases value with
  | empty => simp only [profile, Option.some.injEq] at pure; subst names; simp [Value.free]
  | reference own => simp only [profile, Option.some.injEq] at pure; subst names; rfl
  | node | mu => simp [profile] at pure
  | union entry members depth free =>
      have combined : many members = some names := by simpa only [profile] using pure
      rw [Value.free, union_free state coherent entry members depth free available.resident, childFree_member]
      rw [many_some_member members names combined name]
      apply exists_congr
      intro child
      apply and_congr_right
      intro included
      obtain ⟨refs, childPure⟩ := member_pure members names combined child included
      simpa only [childPure, Option.getD_some] using
        pure_free child state coherent (available.children child included) refs childPure name
termination_by sizeOf value
decreasing_by
  have smaller := List.sizeOf_lt_of_mem included
  simp_wf
  simp_all
  omega

/-- A normalized available source record with one pure root name is exactly that bare reference. -/
theorem profile_single_iff (value : Value Symbol Guard) (state : State Symbol Guard)
    (normal : Normal state) (available : Available state value) (name : Reference) :
    Single name ((profile value).getD []) ↔ value = .reference name := by
  cases value with
  | empty | node | mu => simp [profile, Single]
  | reference own => simp [profile, Single, eq_comm]
  | union entry members depth free =>
      constructor
      · intro single
        cases combined : many members with
        | none => simp [profile, combined, Single] at single
        | some names =>
            have singles : Single name names := by simpa only [profile, combined, Option.getD_some] using single
            have only : ∀ child ∈ members, child = .reference name := by
              intro child included
              have atomic := resident_flat state normal.flat _ available.resident child included
              have nonempty := resident_membersNonempty state normal.members _ available.resident child included
              obtain ⟨refs, pure⟩ := member_pure members names combined child included
              have all : ∀ other ∈ refs, other = name := by
                intro other member
                apply singles.2 other
                exact (many_some_member members names combined other).mpr
                  ⟨child, included, by simpa only [pure, Option.getD_some] using member⟩
              cases child with
              | empty => simp [MemberNonempty, Value.referenceOf] at nonempty
              | reference own =>
                  have same : [own] = refs := by simpa only [profile, Option.some.injEq] using pure
                  have ownPresent : own ∈ refs := by simp [← same]
                  rw [all own ownPresent]
              | node | mu => simp [profile] at pure
              | union => exact False.elim atomic
            obtain ⟨length, unique⟩ := resident_nonempty state normal.proper _ available.resident
            cases members with
            | nil => simp at length
            | cons first rest =>
                cases rest with
                | nil => simp at length
                | cons second tail =>
                    have firstSame := only first List.mem_cons_self
                    have secondSame := only second (by simp)
                    have apart := (List.nodup_cons.mp unique).1
                    exact False.elim (apart (by simp [firstSame, secondSame]))
      · intro impossible; cases impossible

end MicroCFTA.InternedRootProfileReflection
