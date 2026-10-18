import MicroCFTA.SourceCurrentCausalHistoryProfiles
import MicroCFTA.SourceCurrentEmptyProjectionInputs
import MicroCFTA.SourceCurrentFilteredSourceFusion

/-!
# Causal filtered source Empty agreement

An actual reader history derives the stored recursive payload contract.
Paired lexical Empty tests then compare arbitrary completed source calls.
Actual reader filters retain the standalone-reference exception. Stored
execution retains the resulting physical Empty test. This theorem does
not assert agreement of recursive guards or ordered child languages.
-/
namespace MicroCFTA.SourceCurrentCausalFilteredSourceFusion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedFreshOrdinaryLiveInputs (input)
open InternedStoredSubstitution (Environment Replacements leaves encode)
open InternedRootProfile (Profile profile Equivalent)
open InternedProfileSemantics (isEmpty)
open InternedBinderProtocol (Reference)
open SourceCurrentReaderReplacementSlots (Paired)
open SourceCurrentUsedBinderAliasTransport (Scope Aliases)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredRootDeletion (deleted)
open SourceCurrentStoredProfileEmptyProjection (canonical)
open SourceEqualityRequiredCache (Ready)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual stored call reflects the assigned profile's physical Empty test. -/
theorem execute_empty (value : Value Symbol Guard) (environment : Environment Symbol Guard)
    (before : State Symbol Guard) (ready : Ready before) (available : Available before value)
    (replacements : Replacements before environment) (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute value environment before = .done result after) :
    (result.referenceOf == .empty) =
      isEmpty (denote value (fun name => profile ((environment name).getD (.reference name)))) := by
  have context : InternedFreshOrdinaryContext.Context before ((leaves value).map (InternedStoredSubstitution.input environment)) :=
    ⟨ready.semantic.1.normal, InternedStoredSubstitution.inputs_available value environment before available replacements,
      ready.semantic.1.profiles, ready.semantic.1.freeNames⟩
  have called : build (encode (leaves value) [] value) _ before = .done result after := actual
  have kept : InternedFreshOrdinaryContext.Context after ((leaves value).map (InternedStoredSubstitution.input environment)) := by
    simpa only [called, Outcome.state] using context.build (encode (leaves value) [] value)
  have output := (InternedFreshOrdinaryFacts.build_verified (encode (leaves value) [] value) _ before
    context.normal.facts context.inputs).result result after called
  rw [← InternedRootProfileNode.isEmpty_profile result after kept.normal.proper output]
  exact InternedProfileComposition.isEmpty_same
    (SourceCurrentStoredProfileFunction.execute value environment before ready available replacements result after actual)

/-- Causal source calls retain physical Empty agreement through actual warm filters and reconstruction. -/
def Fusion (expression : Syntax Symbol Guard) : Prop :=
  ∀ {Atom : Type} (reader : State Symbol Guard) (_ready : Ready reader) (_history : History empty reader)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (firstOwn secondOwn : Reference) (firstMap secondMap : Environment Symbol Guard)
    (firstBefore secondBefore firstRawHeap secondRawHeap : State Symbol Guard)
    (firstRaw secondRaw firstFiltered secondFiltered left right : Value Symbol Guard),
    Context firstBefore (inputs.map (input firstNames)) →
    Context secondBefore (inputs.map (input secondNames)) →
    Aliases expression inputs firstNames secondNames →
    (∀ label ∈ Scope expression inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn) →
    Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) firstMap secondMap
      (inputs.map (input firstNames)) (inputs.map (input secondNames)) →
    Replacements reader firstMap → Replacements reader secondMap →
    Available reader firstRaw → Available reader secondRaw →
    build expression (inputs.map (input firstNames)) firstBefore = .done firstRaw firstRawHeap →
    build expression (inputs.map (input secondNames)) secondBefore = .done secondRaw secondRawHeap →
    Grows firstRawHeap reader → Grows secondRawHeap reader →
    run (withoutSelfReference firstOwn firstRaw) reader = (firstFiltered, reader) →
    run (withoutSelfReference secondOwn secondRaw) reader = (secondFiltered, reader) →
    execute firstFiltered firstMap reader = .done left reader →
    execute secondFiltered secondMap reader = .done right reader →
    (left.referenceOf == .empty) = (right.referenceOf == .empty)

/-- Every source expression satisfies causal filtered Empty fusion, including nested binders. -/
theorem source (expression : Syntax Symbol Guard) : Fusion expression := by
  intro Atom reader ready history inputs firstNames secondNames firstOwn secondOwn firstMap secondMap
    firstBefore secondBefore firstRawHeap secondRawHeap firstRaw secondRaw firstFiltered secondFiltered left right
    firstContext secondContext aliases tests paired firstReplacements secondReplacements firstAvailable secondAvailable
    firstBuild secondBuild firstGrowth secondGrowth firstFilter secondFilter firstDone secondDone
  let firstAssignment : Reference → Profile := fun name => profile ((firstMap name).getD (.reference name))
  let secondAssignment : Reference → Profile := fun name => profile ((secondMap name).getD (.reference name))
  have profiles : SourceCurrentScopedProfileInputs.Compatible expression inputs firstNames secondNames
      (canonical firstAssignment) (canonical secondAssignment) :=
    SourceCurrentEmptyProjectionInputs.compatible reader ready expression inputs firstNames secondNames
      firstMap secondMap paired firstReplacements secondReplacements
  have compare (firstCuts secondCuts : Reference → Bool)
      (cuts : SourceCurrentScopedDeletionInputs.Compatible expression inputs firstNames secondNames firstCuts secondCuts) :
      Equivalent (deleted firstCuts firstRaw (canonical firstAssignment))
        (deleted secondCuts secondRaw (canonical secondAssignment)) :=
    SourceCurrentCausalHistoryProfiles.compare expression reader history inputs firstNames secondNames
      (canonical firstAssignment) (canonical secondAssignment) firstCuts secondCuts
      firstBefore firstRawHeap secondBefore secondRawHeap firstRaw secondRaw firstContext secondContext
      aliases profiles cuts firstBuild secondBuild firstGrowth secondGrowth
  have localCuts : SourceCurrentScopedDeletionInputs.Compatible expression inputs firstNames secondNames
      (fun name => name == firstOwn) (fun name => name == secondOwn) := by
    constructor
    · intro name member
      apply Bool.eq_iff_iff.mpr
      simpa only [beq_iff_eq, Sum.elim_inl, id_eq] using tests (.inl name) (List.mem_cons_of_mem _ member)
    · intro atom member
      apply Bool.eq_iff_iff.mpr
      simpa only [beq_iff_eq, Sum.elim_inr] using tests (.inr atom) (List.mem_cons_of_mem _ member)
  have bare : firstRaw = .reference firstOwn ↔ secondRaw = .reference secondOwn :=
    SourceCurrentUsedBinderOutputTags.bare expression inputs firstNames secondNames firstOwn secondOwn
      firstBefore firstRawHeap secondBefore secondRawHeap firstContext.base secondContext.base firstRaw secondRaw
      firstBuild secondBuild tests
  have core : Equivalent
      (if firstRaw.referenceOf == .ref firstOwn then canonical firstAssignment firstOwn
        else deleted (fun name => name == firstOwn) firstRaw (canonical firstAssignment))
      (if secondRaw.referenceOf == .ref secondOwn then canonical secondAssignment secondOwn
        else deleted (fun name => name == secondOwn) secondRaw (canonical secondAssignment)) := by
    by_cases firstBare : firstRaw = .reference firstOwn
    · have secondBare := bare.mp firstBare
      have uncut := compare (fun _ => false) (fun _ => false) ⟨fun _ _ => rfl, fun _ _ => rfl⟩
      simpa only [firstBare, secondBare, Value.referenceOf, beq_self_eq_true, ite_true,
        deleted, Bool.false_eq_true, ite_false] using uncut
    · have secondBare : secondRaw ≠ .reference secondOwn := fun same => firstBare (bare.mpr same)
      have firstTag : (firstRaw.referenceOf == .ref firstOwn) = false :=
        Bool.eq_false_iff.mpr (fun same => firstBare ((referenceOf_self_iff firstOwn firstRaw).mp (eq_of_beq same)))
      have secondTag : (secondRaw.referenceOf == .ref secondOwn) = false :=
        Bool.eq_false_iff.mpr (fun same => secondBare ((referenceOf_self_iff secondOwn secondRaw).mp (eq_of_beq same)))
      simp only [firstTag, secondTag, Bool.false_eq_true, ite_false]
      exact compare _ _ localCuts
  have firstFilteredProfile := SourceCurrentStoredRootDeletionConstruction.filter_profile firstOwn firstRaw
    (canonical firstAssignment) reader ready.semantic.1.normal firstAvailable
  have secondFilteredProfile := SourceCurrentStoredRootDeletionConstruction.filter_profile secondOwn secondRaw
    (canonical secondAssignment) reader ready.semantic.1.normal secondAvailable
  rw [firstFilter] at firstFilteredProfile
  rw [secondFilter] at secondFilteredProfile
  have firstFilteredAvailable : Available reader firstFiltered := by
    apply (InternedNestedFacts.filter_verified firstOwn firstRaw reader ready.semantic.1.normal.facts firstAvailable).result
      firstFiltered reader
    simp only [work, firstFilter]
  have secondFilteredAvailable : Available reader secondFiltered := by
    apply (InternedNestedFacts.filter_verified secondOwn secondRaw reader ready.semantic.1.normal.facts secondAvailable).result
      secondFiltered reader
    simp only [work, secondFilter]
  rw [execute_empty firstFiltered firstMap reader ready firstFilteredAvailable firstReplacements left reader firstDone,
    execute_empty secondFiltered secondMap reader ready secondFilteredAvailable secondReplacements right reader secondDone]
  change isEmpty (denote firstFiltered firstAssignment) = isEmpty (denote secondFiltered secondAssignment)
  rw [SourceCurrentStoredProfileEmptyProjection.denote_canonical firstFiltered firstAssignment,
    SourceCurrentStoredProfileEmptyProjection.denote_canonical secondFiltered secondAssignment]
  exact InternedProfileComposition.isEmpty_same (InternedProfileEquivalence.trans firstFilteredProfile
    (InternedProfileEquivalence.trans core (InternedProfileEquivalence.symm secondFilteredProfile)))

end MicroCFTA.SourceCurrentCausalFilteredSourceFusion
