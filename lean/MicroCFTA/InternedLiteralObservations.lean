import MicroCFTA.InternedProfileReferenceInputs
import MicroCFTA.InternedSpecialKeyReadiness
import MicroCFTA.InternedProfileOrigins
import MicroCFTA.InternedFilterSelfReference

/-!
# Actual source observations under arbitrary literal-reference aliases

Equal-length lexical inputs preserve EmptyNode for full nested syntax.
A fresh local returned directly maps to every selected target local,
including a target that aliases an earlier captured reference. These
results use the actual source profile theorem at each execution prefix.
-/
namespace MicroCFTA.InternedLiteralObservations
open InternedConstructorTemplates InternedNestedConstruction InternedNestedMissReadback
open InternedNestedProvenance InternedProbeProvenance InternedStoredMuOrigins
open InternedProfileTraceSites InternedSpecialKeyReadiness InternedSpecialProbeKeys
open InternedRootProfile InternedProfileSemantics InternedProfileCallbackForm
open InternedProfileEquivalence InternedActualProbeTags InternedTwoProbeProfiles
open InternedCallbackTransport InternedRootProfileNode InternedRootProfileReflection
open InternedBinderProtocol (Reference)

/-- The pure empty test reflects its exact profile constructor. -/
theorem empty_test (value : Profile) : isEmpty value = true ↔ value = some [] := by
  cases value with
  | none => simp [isEmpty]
  | some names => cases names <;> simp [isEmpty]

/-- Complete full-syntax executions agree on EmptyNode under all equal-length literal inputs. -/
theorem build_empty [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (firstNames secondNames : List Reference) (length : firstNames.length = secondNames.length)
    (left right afterLeft afterRight : State Symbol Guard)
    (lc : Context left (firstNames.map Value.reference)) (rc : Context right (secondNames.map Value.reference))
    (first second : Value Symbol Guard)
    (firstDone : build expression (firstNames.map Value.reference) left = .done first afterLeft)
    (secondDone : build expression (secondNames.map Value.reference) right = .done second afterRight) :
    first = .empty ↔ second = .empty := by
  have leftChecked := InternedNestedProfiles.build_profile expression _ left lc.normal lc.inputs lc.heap
  have rightChecked := InternedNestedProfiles.build_profile expression _ right rc.normal rc.inputs rc.heap
  have leftNormal : Normal afterLeft := by simpa only [firstDone, Outcome.state] using (lc.build expression).normal
  have rightNormal : Normal afterRight := by simpa only [secondDone, Outcome.state] using (rc.build expression).normal
  have leftAvailable := (build_verified expression _ left lc.normal.facts lc.inputs).result first afterLeft firstDone
  have rightAvailable := (build_verified expression _ right rc.normal.facts rc.inputs).result second afterRight secondDone
  have leftSame := leftChecked.result first afterLeft firstDone
  have rightSame := rightChecked.result second afterRight secondDone
  rw [reference_profiles] at leftSame rightSame
  have emptySame := InternedProfileReferenceInputs.isEmpty_equal_length expression firstNames secondNames length
  have profiles : (evaluate expression (firstNames.map (fun name => some [name])) = some []) ↔
      (evaluate expression (secondNames.map (fun name => some [name])) = some []) := by
    rw [← empty_test, ← empty_test, emptySame]
  rw [← profile_empty_iff first afterLeft leftNormal.proper leftAvailable,
    ← profile_empty_iff second afterRight rightNormal.proper rightAvailable,
    InternedProfileComposition.empty_same leftSame, InternedProfileComposition.empty_same rightSame]
  exact profiles

/-- Every selected local gives the same empty callback result, even when capture aliases differ. -/
theorem callback_empty [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (firstNames secondNames : List Reference) (length : firstNames.length = secondNames.length)
    (firstName secondName : Reference) (left right afterLeft afterRight : State Symbol Guard)
    (lc : Context left (firstNames.map Value.reference)) (rc : Context right (secondNames.map Value.reference))
    (la : Available left (.reference firstName)) (ra : Available right (.reference secondName))
    (first second : Value Symbol Guard)
    (firstDone : callback body (firstNames.map Value.reference) firstName left = .done first afterLeft)
    (secondDone : callback body (secondNames.map Value.reference) secondName right = .done second afterRight) :
    first = .empty ↔ second = .empty := by
  obtain ⟨leftNormal, leftAvailable, leftSame⟩ := callback_completed body _ firstName left lc.normal lc.inputs la lc.heap first afterLeft firstDone
  obtain ⟨rightNormal, rightAvailable, rightSame⟩ := callback_completed body _ secondName right rc.normal rc.inputs ra rc.heap second afterRight secondDone
  rw [reference_profiles] at leftSame rightSame
  rw [← profile_empty_iff first afterLeft leftNormal.proper leftAvailable,
    ← profile_empty_iff second afterRight rightNormal.proper rightAvailable,
    InternedProfileComposition.empty_same leftSame, InternedProfileComposition.empty_same rightSame,
    InternedProfileRenaming.normalized_empty, InternedProfileRenaming.normalized_empty]
  have emptySame := InternedProfileReferenceInputs.isEmpty_equal_length body (firstName :: firstNames) (secondName :: secondNames) (by simp [length])
  simp only [List.map_cons] at emptySame
  rw [← empty_test, ← empty_test, emptySame]

/-- A fresh source local returned directly stays direct under arbitrary target capture aliases. -/
theorem callback_self_forward [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (firstNames secondNames : List Reference) (length : firstNames.length = secondNames.length)
    (firstName secondName : Reference) (fresh : firstName ∉ firstNames)
    (left right afterLeft afterRight : State Symbol Guard)
    (lc : Context left (firstNames.map Value.reference)) (rc : Context right (secondNames.map Value.reference))
    (la : Available left (.reference firstName)) (ra : Available right (.reference secondName))
    (first second : Value Symbol Guard)
    (firstDone : callback body (firstNames.map Value.reference) firstName left = .done first afterLeft)
    (secondDone : callback body (secondNames.map Value.reference) secondName right = .done second afterRight)
    (bare : first = .reference firstName) : second = .reference secondName := by
  obtain ⟨leftNormal, leftAvailable, leftSame⟩ := callback_completed body _ firstName left lc.normal lc.inputs la lc.heap first afterLeft firstDone
  obtain ⟨rightNormal, rightAvailable, rightSame⟩ := callback_completed body _ secondName right rc.normal rc.inputs ra rc.heap second afterRight secondDone
  rw [reference_profiles] at leftSame rightSame
  have firstClass : Classified body (firstNames.map (fun name => some [name])) true := by
    cases computed : symbolic body (firstNames.map (fun name => some [name])) with
    | none =>
        have hidden : profile first = none := leftSame.1.mpr (by rw [opaque_form body _ computed]; rfl)
        simp [bare, profile] at hidden
    | some names =>
        have capturedFresh : firstName ∉ captures names := by
          apply InternedProfileOrigins.captures_fresh body _ names computed firstName
          intro item member
          obtain ⟨name, included, rfl⟩ := List.mem_map.mp member
          simpa using fun same : firstName = name => fresh (same.symm ▸ included)
        have form := trans leftSame (normalize_same firstName (pure_form body _ names computed firstName))
        have single := (self_form first afterLeft leftNormal leftAvailable _ _ _ form).mp bare
        rw [probe, normalize_single, response_single _ _ _ capturedFresh] at single
        exact ⟨names, computed, single.1, single.2⟩
  have secondClass := (InternedProfileReferenceInputs.classified_equal_length body firstNames secondNames length true).mp firstClass
  obtain ⟨names, computed, noCaptures, uses⟩ := secondClass
  have form := trans rightSame (normalize_same secondName (pure_form body _ names computed secondName))
  apply (self_form second afterRight rightNormal rightAvailable _ _ _ form).mpr
  simp [noCaptures, uses, probe, normalize, response, Single]

/-- The same fresh-local observation holds before source root normalization. -/
theorem build_self_forward [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (firstNames secondNames : List Reference) (length : firstNames.length = secondNames.length)
    (firstName secondName : Reference) (fresh : firstName ∉ firstNames)
    (left right afterLeft afterRight : State Symbol Guard)
    (lc : Context left (firstNames.map Value.reference)) (rc : Context right (secondNames.map Value.reference))
    (la : Available left (.reference firstName)) (ra : Available right (.reference secondName))
    (second : Value Symbol Guard)
    (firstDone : build body (.reference firstName :: firstNames.map Value.reference) left = .done (.reference firstName) afterLeft)
    (secondDone : build body (.reference secondName :: secondNames.map Value.reference) right = .done second afterRight) :
    second = .reference secondName := by
  let filtered := run (withoutSelfReference secondName second) afterRight
  have firstCallback : callback body (firstNames.map Value.reference) firstName left = .done (.reference firstName) afterLeft := by
    simp only [callback, firstDone, Outcome.bind, work, withoutSelfReference, run]
  have secondCallback : callback body (secondNames.map Value.reference) secondName right = .done filtered.1 filtered.2 := by
    simp only [callback, secondDone, Outcome.bind, work, filtered]
  have bare := callback_self_forward body firstNames secondNames length firstName secondName fresh
    left right afterLeft filtered.2 lc rc la ra (.reference firstName) filtered.1 firstCallback secondCallback rfl
  have all : Values right (.reference secondName :: secondNames.map Value.reference) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact ra
    · exact rc.inputs value member
  have verified := build_verified body _ right rc.normal.facts all
  have normal : Normal afterRight := by
    simpa only [secondDone, Outcome.state] using build_normal body _ right rc.normal all
  exact (InternedFilterSelfReference.filter_self_iff secondName second afterRight normal.facts.coherent normal.flat
    (verified.result second afterRight secondDone)).mp bare

end MicroCFTA.InternedLiteralObservations
