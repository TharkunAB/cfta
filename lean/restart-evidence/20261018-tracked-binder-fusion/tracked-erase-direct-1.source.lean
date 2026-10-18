import MicroCFTA.SourceCurrentTrackedRootProfile
import MicroCFTA.SourceCurrentStoredMuTrackedProfile

/-!
# Tracked root profiles after local marker erasure

Erase the local marker before observing the outer markers. This gives the
same profile as observing the extended marker list before erasure. The
local marker can also occur in the outer marker list. Actual open Mu
executions then transfer an explicit strict-body tracked comparison to
their whole results. This is not a general source binder fusion law.
-/
namespace MicroCFTA.SourceCurrentTrackedProfileErasure
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (Reference NodeKey)
open InternedRootProfile (Profile profile Equivalent)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements leaves input)
open SourceCurrentStoredMuLexicalInputs (shadow)
open SourceCurrentStoredMuTrackedProfile (erase)
open SourceCurrentTrackedRootProfile (mask observe Related)
open SourceEqualityRequiredCache (Ready)

/-- Erasing the local marker commutes with tracking the outer marker list. -/
theorem mask_erase (marker : Reference) (markers : List Reference) (value : Profile) :
    mask markers (erase marker value) = erase marker (mask (marker :: markers) value) := by
  cases value with
  | none => rfl
  | some names =>
      have all : (names.filter (· != marker)).all markers.contains = names.all (marker :: markers).contains := by
        induction names with
        | nil => rfl
        | cons name names ih =>
            by_cases same : name = marker
            · subst name
              simp [ih]
            · simp [same,Ne.symm same,ih]
      cases selected : names.all (marker :: markers).contains <;>
        simp [erase,mask,all,selected]

private theorem erase_equivalent (marker : Reference) {first second : Profile}
    (same : Equivalent first second) : Equivalent (erase marker first) (erase marker second) := by
  cases first with
  | none =>
      have missing := same.1.mp rfl
      subst second
      exact InternedProfileEquivalence.refl _
  | some first =>
      cases second with
      | none => simp [Equivalent] at same
      | some second =>
          constructor
          · simp [erase]
          · intro name
            have member : name ∈ first ↔ name ∈ second := same.2 name
            simp [erase,member]

/-- Extended tracked profile agreement survives erasure under the outer observation. -/
theorem equivalent (marker : Reference) (markers : List Reference) {first second : Profile}
    (same : Equivalent (mask (marker :: markers) first) (mask (marker :: markers) second)) :
    Equivalent (mask markers (erase marker first)) (mask markers (erase marker second)) := by
  rw [mask_erase,mask_erase]
  exact erase_equivalent marker same

/-- Two actual open Mu executions inherit an explicit tracked comparison of their strict bodies. -/
theorem open_execute [DecidableEq (EdgeKey Symbol Guard)]
    (marker : Reference) (markers : List Reference)
    (firstEntry secondEntry : Interned NodeKey)
    (firstBody firstDepth firstOrdinary secondBody secondDepth secondOrdinary : Value Symbol Guard)
    (firstMap secondMap : Environment Symbol Guard) (firstBefore secondBefore : State Symbol Guard)
    (firstReady : Ready firstBefore) (secondReady : Ready secondBefore)
    (firstAvailable : Available firstBefore (.mu firstEntry firstBody firstDepth firstOrdinary))
    (secondAvailable : Available secondBefore (.mu secondEntry secondBody secondDepth secondOrdinary))
    (firstReplacements : Replacements firstBefore firstMap) (secondReplacements : Replacements secondBefore secondMap)
    (firstOpen : (Value.mu firstEntry firstBody firstDepth firstOrdinary).free.isEmpty = false)
    (secondOpen : (Value.mu secondEntry secondBody secondDepth secondOrdinary).free.isEmpty = false)
    (firstMarker : Available firstBefore (.reference marker)) (secondMarker : Available secondBefore (.reference marker))
    (firstFresh : ∀ leaf ∈ leaves firstBody, marker ∉ (profile (input firstMap leaf)).getD [])
    (secondFresh : ∀ leaf ∈ leaves secondBody, marker ∉ (profile (input secondMap leaf)).getD [])
    (left right : Value Symbol Guard) (firstAfter secondAfter : State Symbol Guard)
    (firstActual : execute (.mu firstEntry firstBody firstDepth firstOrdinary) firstMap firstBefore = .done left firstAfter)
    (secondActual : execute (.mu secondEntry secondBody secondDepth secondOrdinary) secondMap secondBefore = .done right secondAfter)
    (firstResult secondResult : Value Symbol Guard) (firstBodyHeap secondBodyHeap : State Symbol Guard)
    (firstDone : execute firstBody (shadow (.interned firstEntry.identity) (.reference marker) firstMap) firstBefore =
      .done firstResult firstBodyHeap)
    (secondDone : execute secondBody (shadow (.interned secondEntry.identity) (.reference marker) secondMap) secondBefore =
      .done secondResult secondBodyHeap)
    (bodies : Related (marker :: markers) firstResult secondResult) : Related markers left right := by
  have first := SourceCurrentStoredMuTrackedProfile.open_execute firstEntry firstBody firstDepth firstOrdinary
    firstMap firstBefore firstReady firstAvailable firstReplacements firstOpen marker firstMarker firstFresh
    left firstAfter firstActual firstResult firstBodyHeap firstDone
  have second := SourceCurrentStoredMuTrackedProfile.open_execute secondEntry secondBody secondDepth secondOrdinary
    secondMap secondBefore secondReady secondAvailable secondReplacements secondOpen marker secondMarker secondFresh
    right secondAfter secondActual secondResult secondBodyHeap secondDone
  have removed := equivalent marker markers bodies
  exact InternedProfileEquivalence.trans (SourceCurrentTrackedRootProfile.mask_equiv markers first)
    (InternedProfileEquivalence.trans removed
      (InternedProfileEquivalence.symm (SourceCurrentTrackedRootProfile.mask_equiv markers second)))

end MicroCFTA.SourceCurrentTrackedProfileErasure
