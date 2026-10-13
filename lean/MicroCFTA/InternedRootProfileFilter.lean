import MicroCFTA.InternedProfileErasure
import MicroCFTA.InternedRootProfileReflection
import MicroCFTA.InternedRootProfileUnion

/-!
# Root profiles follow the actual source self filter

An actual stored union cannot be a hidden direct-self singleton. Its
normalization therefore erases the selected name. The complete source
union readback then proves the profile equation on both filter branches.
-/
namespace MicroCFTA.InternedRootProfileFilter
open InternedConstructorTemplates InternedRootProfile InternedRootProfileLists
open InternedProfileErasure InternedProfileEquivalence InternedRootProfileReflection
open InternedStoredMuOrigins InternedProbeProvenance InternedUnionNormalForm
open InternedBinderProtocol (Reference)

/-- A proper available union cannot use the all-self exception in profile normalization. -/
theorem union_normalize (name : Reference) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state (.union entry members depth free)) :
    normalize name (many members) = erase name (many members) := by
  cases computed : many members with
  | none => rfl
  | some names =>
      have notAll : names.all (· == name) = false := by
        cases all : names.all (· == name) with
        | false => rfl
        | true =>
            cases names with
            | nil =>
                have emptyProfile : profile (.union entry members depth free) = some [] := by simpa only [profile] using computed
                have impossible := (InternedRootProfileNode.profile_empty_iff _ state normal.proper available).mp emptyProfile
                cases impossible
            | cons head rest =>
                have allNames : ∀ other ∈ head :: rest, other = name := by
                  intro other member
                  simpa using List.all_eq_true.mp all other member
                have headSame := allNames head (by simp)
                have single : Single name ((profile (.union entry members depth free)).getD []) := by
                  simpa only [profile, computed, Option.getD_some, Single] using
                    (⟨by simp [headSame], allNames⟩ : Single name (head :: rest))
                have impossible := (profile_single_iff _ state normal available name).mp single
                cases impossible
      simp [normalize, erase, notAll]

/-- The actual source root filter has exactly the stated profile normalization. -/
theorem filter_profile [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state value) :
    Equivalent (profile (run (withoutSelfReference name value) state).1) (normalize name (profile value)) := by
  cases value with
  | empty => simp [withoutSelfReference, run, profile, normalize, Equivalent]
  | reference other =>
      by_cases same : other = name <;> simp [withoutSelfReference, run, profile, normalize, Equivalent, same]
  | node | mu => simp [withoutSelfReference, run, profile, normalize, Equivalent]
  | union entry members depth free =>
      have atomic := resident_flat state normal.flat (.union entry members depth free) available.resident
      have normalized := union_normalize name entry members depth free state normal available
      simp only [profile] at normalized ⊢
      rw [normalized]
      cases present : members.any (fun member => member.referenceOf == .ref name) with
      | true =>
          simp only [withoutSelfReference, present, ↓reduceIte]
          have selected : InternedNestedProvenance.Values state (members.filter (fun member => member.referenceOf != .ref name)) :=
            fun child member => available.children child (List.mem_filter.mp member).1
          have result := InternedRootProfileUnion.makeUnion_profile _ state normal.facts normal.live normal.proper selected
          rw [many_remove name members atomic] at result
          exact result
      | false =>
          have unchanged : members.filter (fun member => member.referenceOf != .ref name) = members := by
            apply List.filter_eq_self.mpr
            intro child member
            have different : child.referenceOf ≠ .ref name := by
              intro same
              have impossible : members.any (fun member => member.referenceOf == .ref name) = true :=
                List.any_eq_true.mpr ⟨child, member, by simp [same]⟩
              simp [present] at impossible
            simpa using different
          have erased : erase name (many members) = many members := by
            rw [← many_remove name members atomic, unchanged]
          rw [erased]
          simp only [withoutSelfReference, present, Bool.false_eq_true, ↓reduceIte, run, profile]
          exact refl _

end MicroCFTA.InternedRootProfileFilter
