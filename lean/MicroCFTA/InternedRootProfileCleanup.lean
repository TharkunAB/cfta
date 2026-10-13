import MicroCFTA.InternedRootProfileReflection
import MicroCFTA.InternedProfileEquivalence

/-!
# Actual smart cleanup has the decoded capture profile

A fresh local differs from every fixed captured name. A nonempty captured
profile therefore makes the actual body unused by that local. Empty
captures give exactly the empty-body and bare-self cleanup cases. Opaque
bodies remain opaque through every cleanup branch.
-/
namespace MicroCFTA.InternedRootProfileCleanup
open Cache InternedConstructorTemplates InternedNestedConstruction InternedRootProfile
open InternedRootProfileNode InternedRootProfileReflection InternedStoredMuOrigins
open InternedProbeProvenance InternedTwoProbeProfiles InternedProbeDecoder InternedProfileCallbackForm
open InternedBinderProtocol (Reference NodeKey)

/-- A profile equivalent to the empty pure profile is exactly that profile. -/
theorem equivalent_empty {value : Profile} (same : Equivalent value (some [])) : value = some [] := by
  cases value with
  | none => have := same.1.mp rfl; contradiction
  | some names =>
      have empty : names = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro name member
        have impossible := (same.2 name).mp member
        simp at impossible
      rw [empty]

/-- A normalized probe at a fresh name preserves a nonempty fixed capture set exactly. -/
theorem fresh_probe (captured : List Reference) (uses : Bool) (own : Reference)
    (nonempty : captured ≠ []) (fresh : own ∉ captured) : Equivalent (probe captured uses own) (some captured) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨names, pure⟩ := probe_pure captured uses own
    simp [pure]
  · intro name
    constructor
    · exact probe_subset captured uses own name nonempty
    · intro member
      have different : name ≠ own := fun same => fresh (same ▸ member)
      exact (normalize_other own name different (response captured uses own)).mpr
        ((response_member captured uses own name).mpr (Or.inl member))

/-- An opaque normalized body stays opaque through actual smart cleanup. -/
theorem opaque_finish (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (hidden : profile body = none) : profile (finish true (.mu entry body depth ordinary)) = none := by
  by_cases unused : .interned entry.identity ∉ body.free
  · simpa [finish, cleanup, unused] using hidden
  · by_cases self : body.referenceOf = .ref (.interned entry.identity)
    · have bare := (referenceOf_self_iff (.interned entry.identity) body).mp self
      simp [bare, profile] at hidden
    · simp [finish, cleanup, unused, self, profile]

/-- A pure normalized actual body cleans up to exactly the fixed capture profile. -/
theorem smart_profile (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state body)
    (captured : List Reference) (uses : Bool) (fresh : .interned entry.identity ∉ captured)
    (same : Equivalent (profile body) (probe captured uses (.interned entry.identity))) :
    Equivalent (profile (finish true (.mu entry body depth ordinary))) (some captured) := by
  by_cases empty : captured = []
  · subst captured
    cases uses with
    | false =>
        have bodyProfile : profile body = some [] := equivalent_empty (by simpa [probe, response, normalize] using same)
        have bodyEmpty := (profile_empty_iff body state normal.proper available).mp bodyProfile
        simp [bodyEmpty, finish, cleanup, Value.free, profile, Equivalent]
    | true =>
        have bodySingle : Single (.interned entry.identity) ((profile body).getD []) := by
          constructor
          · apply (same.2 _).mpr
            simp [probe, response, normalize]
          · intro name member
            have selected := (same.2 name).mp member
            simpa [probe, response, normalize] using selected
        have bare := (profile_single_iff body state normal available (.interned entry.identity)).mp bodySingle
        simp [bare, finish, cleanup, Value.free, Value.referenceOf, profile, Equivalent]
  · have fixed := fresh_probe captured uses (.interned entry.identity) empty fresh
    have bodyFixed : Equivalent (profile body) (some captured) := InternedProfileEquivalence.trans same fixed
    have pure : ∃ names, profile body = some names := by
      cases found : profile body with
      | some names => exact ⟨names, rfl⟩
      | none => have := bodyFixed.1.mp found; contradiction
    obtain ⟨names, bodyProfile⟩ := pure
    have unused : .interned entry.identity ∉ body.free := by
      intro member
      have included := (pure_free body state normal.facts.coherent available names bodyProfile (.interned entry.identity)).mp member
      apply fresh
      apply (bodyFixed.2 _).mp
      simpa only [bodyProfile, Option.getD_some] using included
    simpa [finish, cleanup, unused] using bodyFixed

end MicroCFTA.InternedRootProfileCleanup
