import MicroCFTA.InternedCallbackReflection

/-!
# One-way local reflection permits captured sentinel aliases

A name map can send a fresh local to a sentinel that is also captured.
The direct-local result still maps forward. The converse need not hold.
The full source executor supplies the normalized result profiles used here.
-/
namespace MicroCFTA.InternedCallbackTransport
open InternedConstructorTemplates InternedNestedConstruction InternedNestedMissReadback
open InternedProbeProvenance InternedNestedProvenance InternedStoredMuOrigins
open InternedRootProfile InternedProfileSemantics InternedNestedProfiles InternedProfileExecutionFacts
open InternedProfileRenaming InternedProfileComposition InternedRootProfileNode InternedRootProfileReflection
open InternedBinderProtocol (Reference)

/-- Mapping the selected local preserves a direct-local result even when captured names have the same image. -/
theorem mapped_single_forward (function : Reference → Reference) (first second : Reference)
    (sameLocal : function first = second) (value : Profile) (single : Single first (value.getD [])) :
    Single second ((mapNames function value).getD []) := by
  cases value with
  | none => simp [Single] at single
  | some names =>
      refine ⟨List.mem_map.mpr ⟨first, single.1, sameLocal⟩, ?_⟩
      intro other member
      obtain ⟨name, included, rfl⟩ := List.mem_map.mp member
      rw [single.2 name included, sameLocal]

/-- A complete actual callback derives all final-state and normalized-profile facts from its source execution. -/
theorem callback_completed [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) (argument : Available state (.reference name))
    (heap : InternedProfileHeap.Heap state) (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : callback expression environment name state = .done value final) :
    Normal final ∧ Available final value ∧
      Equivalent (profile value) (normalize name (evaluate expression (some [name] :: environment.map profile))) := by
  have all : Values state (.reference name :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact argument
    · exact inputs value member
  refine ⟨?_, (callback_verified expression environment name state normal.facts all).result value final completed, ?_⟩
  · simpa only [completed, Outcome.state] using callback_normal expression environment name state normal all
  · have checked := callback_checked expression environment name state normal all
      (by simpa only [List.map_cons, profile] using build_profile expression _ state normal all heap)
    exact checked.result value final completed

/-- Actual completed nested callbacks preserve emptiness and send a direct local to its mapped sentinel. -/
theorem callback_observations [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (function : Reference → Reference) (firstName secondName : Reference) (sameLocal : function firstName = secondName)
    (firstEnvironment secondEnvironment : List (Value Symbol Guard))
    (mapped : secondEnvironment.map profile = (firstEnvironment.map profile).map (mapNames function))
    (left right : State Symbol Guard) (ln : Normal left) (rn : Normal right)
    (li : Values left firstEnvironment) (ri : Values right secondEnvironment)
    (la : Available left (.reference firstName)) (ra : Available right (.reference secondName))
    (lh : InternedProfileHeap.Heap left) (rh : InternedProfileHeap.Heap right)
    (first second : Value Symbol Guard) (afterFirst afterSecond : State Symbol Guard)
    (firstDone : callback expression firstEnvironment firstName left = .done first afterFirst)
    (secondDone : callback expression secondEnvironment secondName right = .done second afterSecond) :
    (first.referenceOf = .empty ↔ second.referenceOf = .empty) ∧
      (first = .reference firstName → second = .reference secondName) := by
  obtain ⟨firstNormal, firstAvailable, firstSame⟩ := callback_completed expression firstEnvironment firstName left ln li la lh first afterFirst firstDone
  obtain ⟨secondNormal, secondAvailable, secondSame⟩ := callback_completed expression secondEnvironment secondName right rn ri ra rh second afterSecond secondDone
  have mappedBody := body_mapped expression function firstName secondName sameLocal
    (firstEnvironment.map profile) (secondEnvironment.map profile) mapped
  rw [mappedBody] at secondSame
  constructor
  · rw [InternedEmptyNormalization.reference_empty, InternedEmptyNormalization.reference_empty,
      ← profile_empty_iff first afterFirst firstNormal.proper firstAvailable,
      ← profile_empty_iff second afterSecond secondNormal.proper secondAvailable]
    apply (empty_same firstSame).trans
    apply Iff.trans ?_ (empty_same secondSame).symm
    rw [normalized_empty, normalized_empty, mapped_empty]
  · intro bare
    apply (profile_single_iff second afterSecond secondNormal secondAvailable secondName).mp
    apply (single_equivalent secondName secondSame).mpr
    apply (normalized_single secondName _).mpr
    apply mapped_single_forward function firstName secondName sameLocal
    apply (normalized_single firstName _).mp
    apply (single_equivalent firstName firstSame).mp
    exact (profile_single_iff first afterFirst firstNormal firstAvailable firstName).mpr bare

end MicroCFTA.InternedCallbackTransport
