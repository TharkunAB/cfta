import MicroCFTA.InternedProfileComposition
import MicroCFTA.InternedRootProfileReflection
import MicroCFTA.SourceEqualityRequiredCache

/-!
# Finite tracked root references

Keep pure root references only when every name is tracked. Other nonempty
root alternatives are opaque. An empty tracking list retains only Empty.
Nested scopes can extend the list with a fresh available local marker.
-/
namespace MicroCFTA.SourceCurrentTrackedRootProfile
open InternedConstructorTemplates InternedRootProfile
open InternedBinderProtocol (Reference)
open InternedProfileSemantics (isEmpty)

/-- Keep a pure root profile only when every root name is tracked. -/
def mask (markers : List Reference) : Profile → Profile
  | none => none
  | some names => if names.all markers.contains then some names else none

/-- Observe tracked literal root references and opacity in one value. -/
def observe (markers : List Reference) (value : Value Symbol Guard) : Profile := mask markers (profile value)

/-- Values agree on tracked root reference sets and on opacity. -/
def Related (markers : List Reference) (first second : Value Symbol Guard) : Prop :=
  Equivalent (observe markers first) (observe markers second)

/-- Every value has the same tracked root profile as itself. -/
theorem Related.refl (markers : List Reference) (value : Value Symbol Guard) : Related markers value value :=
  InternedProfileEquivalence.refl _

/-- Reversing a tracked comparison retains its profile equivalence. -/
theorem Related.symm {markers : List Reference} {first second : Value Symbol Guard}
    (same : Related markers first second) : Related markers second first :=
  InternedProfileEquivalence.symm same

/-- Tracking changes no physical empty-list profile decision. -/
theorem mask_empty (markers : List Reference) (value : Profile) : isEmpty (mask markers value) = isEmpty value := by
  cases value with
  | none => rfl
  | some names =>
      cases names with
      | nil => rfl
      | cons first rest =>
          simp only [mask]
          split <;> rfl

/-- Equivalent root profiles retain the same tracked root alternatives. -/
theorem mask_equiv (markers : List Reference) {first second : Profile} (same : Equivalent first second) :
    Equivalent (mask markers first) (mask markers second) := by
  cases first with
  | none =>
      have missing := same.1.mp rfl
      subst second
      exact InternedProfileEquivalence.refl _
  | some left =>
      cases second with
      | none => simp [Equivalent] at same
      | some right =>
          have all : left.all markers.contains = right.all markers.contains := by
            apply Bool.eq_iff_iff.mpr
            simp only [List.all_eq_true]
            exact ⟨fun selected name member => selected name ((same.2 name).mpr member),
              fun selected name member => selected name ((same.2 name).mp member)⟩
          cases selected : right.all markers.contains <;> simp only [mask,all,selected]
          · exact InternedProfileEquivalence.refl _
          · exact same

/-- Tracking commutes with a root union profile fold step. -/
theorem mask_combine (markers : List Reference) (first second : Profile) :
    mask markers (combine first second) = combine (mask markers first) (mask markers second) := by
  cases first with
  | none => rfl
  | some left =>
      cases second with
      | none => cases selected : left.all markers.contains <;> simp [mask,combine,selected]
      | some right =>
          cases one : left.all markers.contains <;> cases two : right.all markers.contains <;>
            simp [mask,combine,List.all_append,one,two]

/-- Tracked profile agreement gives equal physical Empty tests for available values. -/
theorem Related.empty {markers : List Reference} {first second : Value Symbol Guard}
    (same : Related markers first second) (reader : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready reader)
    (firstAvailable : InternedProbeProvenance.Available reader first)
    (secondAvailable : InternedProbeProvenance.Available reader second) :
    (first.referenceOf == .empty) = (second.referenceOf == .empty) := by
  have equal := InternedProfileComposition.isEmpty_same same
  change isEmpty (mask markers (profile first)) = isEmpty (mask markers (profile second)) at equal
  rw [mask_empty,mask_empty,
    InternedRootProfileNode.isEmpty_profile first reader ready.semantic.1.normal.proper firstAvailable,
    InternedRootProfileNode.isEmpty_profile second reader ready.semantic.1.normal.proper secondAvailable] at equal
  exact equal

/-- Ordinary results with equal Empty tests have equal tracked root profiles. -/
theorem ordinary_of_empty (markers : List Reference) (first second : Value Symbol Guard)
    (firstOrdinary : SourceEqualityRequiredCache.Ordinary first)
    (secondOrdinary : SourceEqualityRequiredCache.Ordinary second)
    (equal : (first.referenceOf == .empty) = (second.referenceOf == .empty)) : Related markers first second := by
  cases first <;> cases second <;>
    simp_all [SourceEqualityRequiredCache.Ordinary,Related,observe,profile,mask,Equivalent,Value.referenceOf]

/-- With no tracked markers, profile equivalence retains exactly the Empty decision. -/
theorem nil_equiv (first second : Profile) :
    Equivalent (mask [] first) (mask [] second) ↔ isEmpty first = isEmpty second := by
  cases first with
  | none => cases second with
    | none => simp [mask,isEmpty,Equivalent]
    | some names => cases names <;> simp [mask,isEmpty,Equivalent]
  | some names =>
      cases names <;> cases second with
      | none => simp [mask,isEmpty,Equivalent]
      | some names => cases names <;> simp [mask,isEmpty,Equivalent]

/-- Tracking a marker retains its exact pure singleton test. -/
theorem mask_single (markers : List Reference) (name : Reference) (tracked : name ∈ markers) (value : Profile) :
    Single name ((mask markers value).getD []) ↔ Single name (value.getD []) := by
  cases value with
  | none => rfl
  | some names =>
      by_cases all : names.all markers.contains = true
      · simp only [mask,all,↓reduceIte,Option.getD_some]
      · simp only [mask,Bool.eq_false_iff.mpr all,Bool.false_eq_true,↓reduceIte,Option.getD_none,Option.getD_some]
        constructor
        · intro impossible; cases impossible.1
        · intro single
          apply False.elim
          apply all
          apply List.all_eq_true.mpr
          intro other member
          rw [single.2 other member]
          exact List.contains_iff_mem.mpr tracked

/-- Tracked profile agreement retains a tracked bare reference at an actual normal reader. -/
theorem Related.bare {markers : List Reference} {first second : Value Symbol Guard}
    (same : Related markers first second) (name : Reference) (tracked : name ∈ markers)
    (reader : State Symbol Guard) (ready : SourceEqualityRequiredCache.Ready reader)
    (firstAvailable : InternedProbeProvenance.Available reader first)
    (secondAvailable : InternedProbeProvenance.Available reader second) :
    first = .reference name ↔ second = .reference name := by
  have equal := InternedProfileRenaming.single_equivalent name same
  change Single name ((mask markers (profile first)).getD []) ↔
    Single name ((mask markers (profile second)).getD []) at equal
  rw [mask_single markers name tracked,mask_single markers name tracked,
    InternedRootProfileReflection.profile_single_iff first reader ready.semantic.1.normal firstAvailable name,
    InternedRootProfileReflection.profile_single_iff second reader ready.semantic.1.normal secondAvailable name] at equal
  exact equal

/-- Adding a marker absent from a profile retains the same tracked observation. -/
theorem mask_cons_fresh (marker : Reference) (markers : List Reference) (value : Profile)
    (fresh : marker ∉ value.getD []) : mask (marker :: markers) value = mask markers value := by
  cases value with
  | none => rfl
  | some names =>
      have all : names.all (marker :: markers).contains = names.all markers.contains := by
        apply Bool.eq_iff_iff.mpr
        rw [List.all_eq_true,List.all_eq_true]
        constructor
        · intro selected name member
          have present := List.contains_iff_mem.mp (selected name member)
          rcases List.mem_cons.mp present with same | present
          · exact False.elim (fresh (same ▸ member))
          · exact List.contains_iff_mem.mpr present
        · intro selected name member
          exact List.contains_iff_mem.mpr (List.mem_cons_of_mem _ (List.contains_iff_mem.mp (selected name member)))
      simp only [mask,all]

end MicroCFTA.SourceCurrentTrackedRootProfile
