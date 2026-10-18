import MicroCFTA.SourceCurrentStoredMuMarkerEmpty

/-!
# Full root profiles through actual open Mu cleanup

A real strict-body execution uses a fresh available marker for self.
The complete open Mu result has the same root profile after that marker
is removed at the body result root. Other references remain present.
Ordinary nodes and recursive atoms remain opaque. Freshness uses only
resolved profiles of the finite original body leaves.
-/
namespace MicroCFTA.SourceCurrentStoredMuTrackedProfile
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedProfileSemantics (Abstract evaluate mapNames lower)
open InternedRootProfile (Profile profile Equivalent)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredMuLexicalInputs (shadow)

/-- Remove every occurrence of the marker from a pure root profile and retain opacity. -/
def erase (marker : Reference) (value : Profile) : Profile := value.map (List.filter (· != marker))

private theorem erase_equivalent (marker : Reference) {first second : Profile}
    (same : Equivalent first second) : Equivalent (erase marker first) (erase marker second) := by
  cases first with
  | none =>
      have other := same.1.mp rfl
      subst second
      exact InternedProfileEquivalence.refl _
  | some first =>
      cases second with
      | none => simp [Equivalent] at same
      | some second =>
          constructor
          · simp [erase]
          · intro name
            have members : name ∈ first ↔ name ∈ second := same.2 name
            simp [erase,members]

private theorem erase_mapped (value : Abstract (Sum Unit Reference)) (marker : Reference)
    (fresh : ∀ name, Sum.inr name ∈ value.getD [] → name ≠ marker) :
    erase marker (mapNames (Sum.elim (fun _ : Unit => marker) id) value) = lower value := by
  cases value with
  | none => rfl
  | some names =>
      simp only [erase,mapNames,Option.map_some,lower]
      apply congrArg some
      induction names with
      | nil => rfl
      | cons first rest ih =>
          have tail : ∀ name, Sum.inr name ∈ rest → name ≠ marker :=
            fun name member => fresh name (List.mem_cons_of_mem _ member)
          cases first with
          | inl token => cases token; simp [ih tail]
          | inr name =>
              have different := fresh name List.mem_cons_self
              simp [different,ih tail]

private def symbolic (body : Value Symbol Guard) (own : Reference) (environment : Environment Symbol Guard) :
    Abstract (Sum Unit Reference) :=
  evaluate (encode (leaves body) [] body) ((leaves body).map (fun leaf => match leaf with
    | .reference name => if own = name then some [Sum.inl ()]
        else mapNames Sum.inr (profile (input environment leaf))
    | _ => mapNames Sum.inr (profile (input environment leaf))))

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
      change Sum.inr marker ∈ (if own = name then some [Sum.inl ()]
        else mapNames Sum.inr (profile (input environment (.reference name)))).getD [] at member
      by_cases same : own = name
      · simp only [same,ite_true,Option.getD_some,List.mem_singleton,reduceCtorEq] at member
      · simp only [same,ite_false] at member
        obtain ⟨actual,selected,equal⟩ := (InternedProfileOrigins.mapNames_member Sum.inr _ _).mp member
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

private theorem actual_profile [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before value) (replacements : Replacements before environment)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute value environment before = .done result after) :
    Equivalent (profile result)
      (evaluate (encode (leaves value) [] value) ((leaves value).map (fun leaf => profile (input environment leaf)))) := by
  let inputs := (leaves value).map (input environment)
  let plan := encode (leaves value) [] value
  have context : InternedFreshOrdinaryContext.Context before inputs :=
    ⟨ready.semantic.1.normal,InternedStoredSubstitution.inputs_available value environment before available replacements,
      ready.semantic.1.profiles,ready.semantic.1.freeNames⟩
  have called : InternedFreshOrdinaryConstruction.build plan inputs before = .done result after := actual
  have matched := (InternedFreshOrdinaryProfiles.build_profile plan inputs before context.normal context.inputs context.profiles).result
    result after called
  simpa only [inputs,plan,List.map_map,Function.comp_def] using matched

private theorem open_plan (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before (.mu entry body depth ordinary))
    (opened : (Value.mu entry body depth ordinary).free.isEmpty = false) :
    evaluate (encode (leaves (.mu entry body depth ordinary)) [] (.mu entry body depth ordinary))
      ((leaves (.mu entry body depth ordinary)).map (fun leaf => profile (input environment leaf))) =
      lower (symbolic body (.interned entry.identity) environment) := by
  have collected : leaves (.mu entry body depth ordinary) = leaves body := by
    rw [leaves.eq_def]
    simp only [opened,Bool.false_eq_true,ite_false]
  have encoded : encode (leaves body) [] (.mu entry body depth ordinary) =
      .binder true (encode (leaves body) [.interned entry.identity] body) := by
    rw [encode.eq_def]
    simp only [opened,Bool.false_eq_true,ite_false]
  rw [collected,encoded,evaluate]
  exact congrArg lower (SourceCurrentStoredMuEmptyPlan.rebind_profile body (.interned entry.identity) environment before
    ready.semantic.1.normal.facts.coherent (available.children body (by simp [InternedProbeProvenance.children])))

/-- Actual open Mu execution removes the fresh marker only from the strict body's root profile. -/
theorem open_execute [DecidableEq (EdgeKey Symbol Guard)]
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
    Equivalent (profile result) (erase marker (profile bodyResult)) := by
  have bodyAvailable := available.children body (by simp [InternedProbeProvenance.children])
  have mappedReplacements := SourceCurrentStoredMuLexicalInputs.replacements
    (.interned entry.identity) (.reference marker) environment before before replacements
      (grows_refl _) (extends_refl _) markerAvailable
  have matched := actual_profile body _ before ready bodyAvailable mappedReplacements bodyResult afterBody bodyDone
  have mapped := symbolic_mapped body (.interned entry.identity) marker environment
  have same : Equivalent (profile bodyResult)
      (mapNames (Sum.elim (fun _ : Unit => marker) id) (symbolic body (.interned entry.identity) environment)) := by
    rw [mapped]
    exact matched
  have removed := erase_equivalent marker same
  rw [erase_mapped _ marker (symbolic_fresh body (.interned entry.identity) marker environment fresh)] at removed
  have whole := actual_profile (.mu entry body depth ordinary) environment before ready available replacements result after actual
  rw [open_plan entry body depth ordinary environment before ready available opened] at whole
  exact InternedProfileEquivalence.trans whole (InternedProfileEquivalence.symm removed)

/-- Initial data constructs the strict-body execution and retains the full root-profile comparison. -/
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
      Equivalent (profile result) (erase marker (profile bodyResult)) := by
  have bodyAvailable := available.children body (by simp [InternedProbeProvenance.children])
  have mappedReplacements := SourceCurrentStoredMuLexicalInputs.replacements
    (.interned entry.identity) (.reference marker) environment before before replacements
      (grows_refl _) (extends_refl _) markerAvailable
  obtain ⟨bodyResult,afterBody,bodyDone,kept,output,_⟩ := SourceCurrentStoredReconstruction.execute
    body _ before ready bodyAvailable mappedReplacements
  exact ⟨bodyResult,afterBody,bodyDone,kept,output,open_execute entry body depth ordinary environment before ready available
    replacements opened marker markerAvailable fresh result after actual bodyResult afterBody bodyDone⟩

end MicroCFTA.SourceCurrentStoredMuTrackedProfile
