import MicroCFTA.SourceCurrentStoredMuEmptyPlan
import MicroCFTA.SourceCurrentStoredMuLexicalInputs
import MicroCFTA.SourceCurrentStoredReconstruction

/-!
# Actual strict-body marker tests for stored Mu cleanup

A fresh available reference represents the symbolic self in a real stored
body execution. The open Mu returns Empty exactly when that body returns
Empty or the bare marker. Ordinary nodes remain opaque in this test.
Freshness refers only to the finite list of resolved original body leaves.
This module does not compare two different writer bodies or probes.
-/
namespace MicroCFTA.SourceCurrentStoredMuMarkerEmpty
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedProfileSemantics (Abstract evaluate mapNames lower isEmpty)
open InternedRootProfile (Profile profile Equivalent Single)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredMuLexicalInputs (shadow)

private def symbolic (body : Value Symbol Guard) (own : Reference) (environment : Environment Symbol Guard) :
    Abstract (Sum Unit Reference) :=
  evaluate (encode (leaves body) [] body) ((leaves body).map (fun leaf => match leaf with
    | .reference name => if own = name then some [Sum.inl ()]
        else mapNames Sum.inr (profile (input environment leaf))
    | _ => mapNames Sum.inr (profile (input environment leaf))))

private theorem lower_test (value : Abstract (Sum Unit Reference)) (marker : Reference)
    (fresh : ∀ name, Sum.inr name ∈ value.getD [] → name ≠ marker) :
    isEmpty (lower value) = true ↔
      mapNames (Sum.elim (fun _ : Unit => marker) id) value = some [] ∨
        Single marker ((mapNames (Sum.elim (fun _ : Unit => marker) id) value).getD []) := by
  cases value with
  | none => simp [lower,isEmpty,mapNames,Single]
  | some names =>
      have lowered : isEmpty (lower (some names)) = true ↔ ∀ label ∈ names, label = Sum.inl () := by
        rw [show isEmpty (lower (some names)) = true ↔
          names.filterMap (fun label => match label with | .inl _ => none | .inr name => some name) = [] by
            cases found : names.filterMap (fun label => match label with | .inl _ => none | .inr name => some name) <;>
              simp [lower,isEmpty,found]]
        rw [List.filterMap_eq_nil_iff]
        constructor <;> intro all label member
        · cases label with
          | inl token => cases token; rfl
          | inr name => cases all (.inr name) member
        · rw [all label member]
      rw [lowered]
      simp only [mapNames,Option.map_some,Option.some.injEq,Option.getD_some]
      constructor
      · intro all
        cases names with
        | nil => exact Or.inl rfl
        | cons first rest =>
            right
            refine ⟨?_,?_⟩
            · exact List.mem_map.mpr ⟨first,List.mem_cons_self,by rw [all first List.mem_cons_self]; rfl⟩
            · intro name member
              obtain ⟨label,present,rfl⟩ := List.mem_map.mp member
              rw [all label present]
      · rintro (empty | only) label member
        · have impossible : names = [] := List.map_eq_nil_iff.mp empty
          simp [impossible] at member
        · have same := only.2 _ (List.mem_map.mpr ⟨label,member,rfl⟩)
          cases label with
          | inl token => cases token; rfl
          | inr name => exact False.elim (fresh name member same)

private theorem symbolic_fresh (body : Value Symbol Guard) (own marker : Reference)
    (environment : Environment Symbol Guard)
    (fresh : ∀ leaf ∈ leaves body, marker ∉ (profile (input environment leaf)).getD []) :
    ∀ name, Sum.inr name ∈ (symbolic body own environment).getD [] → name ≠ marker := by
  intro name member same
  subst name
  obtain ⟨value,present,member⟩ := InternedProfileOrigins.evaluate_origin
    (encode (leaves body) [] body) _ (Sum.inr marker) member
  obtain ⟨leaf,included,rfl⟩ := List.mem_map.mp present
  cases leaf with
  | reference name =>
      split at member
      · simp at member
      · obtain ⟨actual,selected,equal⟩ := (InternedProfileOrigins.mapNames_member Sum.inr _ _).mp member
        cases equal
        exact fresh (.reference name) included selected
  | empty | node | union | mu =>
      obtain ⟨actual,selected,equal⟩ := (InternedProfileOrigins.mapNames_member Sum.inr _ _).mp member
      cases equal
      exact fresh _ included selected

private theorem symbolic_mapped (body : Value Symbol Guard) (own marker : Reference)
    (environment : Environment Symbol Guard) :
    mapNames (Sum.elim (fun _ : Unit => marker) id) (symbolic body own environment) =
      evaluate (encode (leaves body) [] body)
        ((leaves body).map (fun leaf => profile (input (shadow own (.reference marker) environment) leaf))) := by
  rw [symbolic,←InternedProfileSemantics.evaluate_map,List.map_map]
  congr 1
  apply List.map_congr_left
  intro leaf _
  cases leaf with
  | reference name =>
      by_cases same : own = name
      · subst name
        simp [shadow,input,profile,mapNames]
      · simp [shadow,input,Ne.symm same,same,mapNames,List.map_map,Function.comp_def]
  | empty | node | union | mu =>
      simp [input,mapNames,List.map_map,Function.comp_def]

private theorem actual_profile [DecidableEq (EdgeKey Symbol Guard)] (body : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before body) (replacements : Replacements before environment)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute body environment before = .done result after) :
    Equivalent (profile result)
      (evaluate (encode (leaves body) [] body) ((leaves body).map (fun leaf => profile (input environment leaf)))) ∧
    InternedStoredMuOrigins.Normal after ∧ Available after result := by
  let inputs := (leaves body).map (input environment)
  let plan := encode (leaves body) [] body
  have context : InternedFreshOrdinaryContext.Context before inputs :=
    ⟨ready.semantic.1.normal,InternedStoredSubstitution.inputs_available body environment before available replacements,
      ready.semantic.1.profiles,ready.semantic.1.freeNames⟩
  have called : InternedFreshOrdinaryConstruction.build plan inputs before = .done result after := actual
  have later : InternedFreshOrdinaryContext.Context after inputs := by
    simpa only [called,Outcome.state] using context.build plan
  have output := (InternedFreshOrdinaryFacts.build_verified plan inputs before context.normal.facts context.inputs).result
    result after called
  have matched := (InternedFreshOrdinaryProfiles.build_profile plan inputs before context.normal context.inputs context.profiles).result
    result after called
  exact ⟨by simpa only [inputs,plan,List.map_map,Function.comp_def] using matched,later.normal,output⟩

/-- Actual open Mu cleanup tests Empty or a bare fresh marker in the reconstructed strict original body. -/
theorem marker_test [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before (.mu entry body depth ordinary)) (replacements : Replacements before environment)
    (opened : (Value.mu entry body depth ordinary).free.isEmpty = false)
    (marker : Reference) (markerAvailable : Available before (.reference marker))
    (fresh : ∀ leaf ∈ leaves body, marker ∉ (profile (input environment leaf)).getD [])
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute (.mu entry body depth ordinary) environment before = .done result after)
    (bodyResult : Value Symbol Guard) (afterBody : State Symbol Guard)
    (bodyDone : execute body (shadow (.interned entry.identity) (.reference marker) environment) before =
      .done bodyResult afterBody) :
    (result.referenceOf == .empty) = true ↔ bodyResult = .empty ∨ bodyResult = .reference marker := by
  have bodyAvailable := available.children body (by simp [InternedProbeProvenance.children])
  have mappedReplacements := SourceCurrentStoredMuLexicalInputs.replacements
    (.interned entry.identity) (.reference marker) environment before before replacements
      (grows_refl _) (extends_refl _) markerAvailable
  obtain ⟨matched,normal,output⟩ := actual_profile body _ before ready bodyAvailable mappedReplacements bodyResult afterBody bodyDone
  have mapped := symbolic_mapped body (.interned entry.identity) marker environment
  have same : Equivalent (profile bodyResult)
      (mapNames (Sum.elim (fun _ : Unit => marker) id) (symbolic body (.interned entry.identity) environment)) := by
    rw [mapped]
    exact matched
  have whole := SourceCurrentStoredMuEmptyPlan.open_execute entry body depth ordinary environment before ready available
    replacements opened result after actual
  change (result.referenceOf == .empty) = isEmpty (lower (symbolic body (.interned entry.identity) environment)) at whole
  rw [whole,lower_test _ marker (symbolic_fresh body (.interned entry.identity) marker environment fresh)]
  rw [←InternedProfileComposition.empty_same same,←InternedProfileRenaming.single_equivalent marker same,
    InternedRootProfileNode.profile_empty_iff bodyResult afterBody normal.proper output,
    InternedRootProfileReflection.profile_single_iff bodyResult afterBody normal output marker]

/-- Initial available data constructs the strict-body marker call and retains its actual reader effects. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before (.mu entry body depth ordinary)) (replacements : Replacements before environment)
    (opened : (Value.mu entry body depth ordinary).free.isEmpty = false)
    (marker : Reference) (markerAvailable : Available before (.reference marker))
    (fresh : ∀ leaf ∈ leaves body, marker ∉ (profile (input environment leaf)).getD [])
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute (.mu entry body depth ordinary) environment before = .done result after) :
    ∃ bodyResult afterBody,
      execute body (shadow (.interned entry.identity) (.reference marker) environment) before = .done bodyResult afterBody ∧
      Keeps before afterBody ∧ Available afterBody bodyResult ∧
      ((result.referenceOf == .empty) = true ↔ bodyResult = .empty ∨ bodyResult = .reference marker) := by
  have bodyAvailable := available.children body (by simp [InternedProbeProvenance.children])
  have mappedReplacements := SourceCurrentStoredMuLexicalInputs.replacements
    (.interned entry.identity) (.reference marker) environment before before replacements
      (grows_refl _) (extends_refl _) markerAvailable
  obtain ⟨bodyResult,afterBody,bodyDone,kept,output,_⟩ := SourceCurrentStoredReconstruction.execute
    body _ before ready bodyAvailable mappedReplacements
  exact ⟨bodyResult,afterBody,bodyDone,kept,output,marker_test entry body depth ordinary environment before ready available
    replacements opened marker markerAvailable fresh result after actual bodyResult afterBody bodyDone⟩

end MicroCFTA.SourceCurrentStoredMuMarkerEmpty
