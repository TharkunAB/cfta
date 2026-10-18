import MicroCFTA.SourceCurrentFilteredSourceFusion
import MicroCFTA.SourceCurrentFilteredUnionCoverage
import MicroCFTA.SourceCurrentUsedBinderOutputTags

/-!
# Filtered union Empty fusion from strict source members

Finite actual member preparation gives both schedules one later reader.
The original source contexts remain at their historical entry states.
Scoped self tests give equal bare-self retention decisions. Strict source
member fusion then gives the exact parent physical Empty agreement.
-/
namespace MicroCFTA.SourceCurrentFilteredUnionFusion
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryLiveInputs (input inputProfile)
open InternedStoredSubstitution (Environment Replacements leaves encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentNativeNormalizationInputs (support inputNames)
open SourceCurrentFilteredSourceFusion (Fusion)

private theorem scope_subset (expressions : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (expression : Syntax Symbol Guard)
    (member : expression ∈ expressions) (label : Sum Reference Atom)
    (found : label ∈ Scope expression inputs) : label ∈ Scope (.union expressions) inputs := by
  rcases List.mem_cons.mp found with rfl | found
  · exact List.mem_cons_self
  · apply List.mem_cons_of_mem
    unfold support at found ⊢
    rw [InternedFreeNameSemantics.evaluate]
    exact (InternedFreeNameSemantics.evaluateMany_member expressions (inputs.map inputProfile)
      (inputs.map inputNames) label).mpr ⟨expression,member,found⟩

private def SourceCall [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Value Symbol Guard))
    (reader : State Symbol Guard) (raw : Value Symbol Guard) : Prop :=
  ∃ before after, Context before inputs ∧ build expression inputs before = .done raw after ∧ Grows after reader

private theorem source_extend [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before after : State Symbol Guard) (growth : Grows before after) (raws : List (Value Symbol Guard))
    (sources : All₂ (fun expression raw => ∃ current returned,
      Context current inputs ∧ build expression inputs current = .done raw returned ∧
        Grows returned before ∧ build expression inputs before = .done raw before) expressions raws) :
    All₂ (fun expression raw => SourceCall expression inputs after raw) expressions raws := by
  induction sources with
  | nil => exact .nil
  | cons first rest ih =>
      obtain ⟨current,returned,context,actual,old,_⟩ := first
      exact .cons ⟨current,returned,context,actual,grows_trans old growth⟩ ih

private theorem filters_replay [DecidableEq (EdgeKey Symbol Guard)] (own : Reference)
    (before after : State Symbol Guard) (valid : Valid before) (growth : Grows before after)
    {raws filters : List (Value Symbol Guard)}
    (calls : All₂ (fun raw filtered => run (withoutSelfReference own raw) before = (filtered,before)) raws filters) :
    All₂ (fun raw filtered => run (withoutSelfReference own raw) after = (filtered,after)) raws filters := by
  induction calls with
  | nil => exact .nil
  | @cons raw filtered raws filters head tail ih =>
      exact .cons (by simpa only [head] using (replay (withoutSelfReference own raw) before after valid
        (by rw [head]; exact growth))) ih

private theorem stored_replay [DecidableEq (EdgeKey Symbol Guard)] (environment : Environment Symbol Guard)
    (before after : State Symbol Guard) (valid : Valid before) (growth : Grows before after)
    {filters outputs : List (Value Symbol Guard)}
    (calls : All₂ (fun filtered output => execute filtered environment before = .done output before) filters outputs) :
    All₂ (fun filtered output => execute filtered environment after = .done output after) filters outputs := by
  induction calls with
  | nil => exact .nil
  | @cons filtered output filters outputs head tail ih =>
      exact .cons (InternedFreshOrdinaryStoredSubstitution.execute_replay filtered environment before after
        output before valid head growth) ih

private theorem member_calls [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard)
    (own : Reference) (environment : Environment Symbol Guard)
    {raws filters outputs : List (Value Symbol Guard)}
    (first : All₂ (fun raw filtered => run (withoutSelfReference own raw) reader = (filtered,reader)) raws filters)
    (second : All₂ (fun filtered output => execute filtered environment reader = .done output reader) filters outputs) :
    ∀ raw ∈ raws, ∃ filtered output,
      run (withoutSelfReference own raw) reader = (filtered,reader) ∧ execute filtered environment reader = .done output reader := by
  induction first generalizing outputs with
  | nil => intro raw impossible; cases impossible
  | cons head tail ih =>
      cases second with
      | cons called rest =>
          intro raw member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨_,_,head,called⟩
          · exact ih rest raw member

private theorem pair_left {A B : Type} {relation : A → B → Prop} {first : List A} {second : List B}
    (paired : All₂ relation first second) (value : A) (member : value ∈ first) :
    ∃ other ∈ second, relation value other := by
  induction paired with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_,List.mem_cons_self,head⟩
      · obtain ⟨other,present,related⟩ := ih member
        exact ⟨other,List.mem_cons_of_mem _ present,related⟩

private theorem pair_right {A B : Type} {relation : A → B → Prop} {first : List A} {second : List B}
    (paired : All₂ relation first second) (value : B) (member : value ∈ second) :
    ∃ other ∈ first, relation other value := by
  induction paired with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_,List.mem_cons_self,head⟩
      · obtain ⟨other,present,related⟩ := ih member
        exact ⟨other,List.mem_cons_of_mem _ present,related⟩

private theorem members_fusion [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (Syntax Symbol Guard)) (ih : ∀ child ∈ expressions, Fusion child)
    (reader : State Symbol Guard) (ready : Ready reader)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (firstOwn secondOwn : Reference) (firstMap secondMap : Environment Symbol Guard)
    (aliases : ∀ child ∈ expressions, Aliases child inputs firstNames secondNames)
    (tests : ∀ child ∈ expressions, ∀ label ∈ Scope child inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn)
    (paired : SourceCurrentReaderReplacementSlots.Paired
      (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) firstMap secondMap
      (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader firstMap) (secondReplacements : Replacements reader secondMap)
    (firstRaws secondRaws : List (Value Symbol Guard))
    (firstSource : All₂ (fun child raw => SourceCall child (inputs.map (input firstNames)) reader raw) expressions firstRaws)
    (secondSource : All₂ (fun child raw => SourceCall child (inputs.map (input secondNames)) reader raw) expressions secondRaws)
    (firstAvailable : Values reader firstRaws) (secondAvailable : Values reader secondRaws) :
    All₂ (fun a b => (a = .reference firstOwn ↔ b = .reference secondOwn) ∧
      ∀ firstFiltered secondFiltered left right,
        run (withoutSelfReference firstOwn a) reader = (firstFiltered,reader) →
        run (withoutSelfReference secondOwn b) reader = (secondFiltered,reader) →
        execute firstFiltered firstMap reader = .done left reader →
        execute secondFiltered secondMap reader = .done right reader →
        (left.referenceOf == .empty) = (right.referenceOf == .empty)) firstRaws secondRaws := by
  induction firstSource generalizing secondRaws with
  | nil => cases secondSource; exact .nil
  | @cons expression raw expressions raws firstSource remaining induct =>
      cases secondSource with
      | @cons _ other _ others secondSource secondRemaining =>
          obtain ⟨before,after,firstContext,firstBuild,firstGrowth⟩ := firstSource
          obtain ⟨later,final,secondContext,secondBuild,secondGrowth⟩ := secondSource
          refine .cons ⟨SourceCurrentUsedBinderOutputTags.bare expression inputs firstNames secondNames firstOwn secondOwn
            before after later final firstContext.base secondContext.base raw other firstBuild secondBuild
            (tests expression List.mem_cons_self),?_⟩ ?_
          · intro firstFiltered secondFiltered left right firstFilter secondFilter firstDone secondDone
            exact ih expression List.mem_cons_self reader ready inputs firstNames secondNames firstOwn secondOwn firstMap secondMap
              before later after final raw other firstFiltered secondFiltered left right firstContext secondContext
              (aliases expression List.mem_cons_self) (tests expression List.mem_cons_self) paired firstReplacements secondReplacements
              (firstAvailable raw List.mem_cons_self) (secondAvailable other List.mem_cons_self)
              firstBuild secondBuild firstGrowth secondGrowth firstFilter secondFilter firstDone secondDone
          · exact induct (fun child member => ih child (List.mem_cons_of_mem _ member))
              (fun child member => aliases child (List.mem_cons_of_mem _ member))
              (fun child member => tests child (List.mem_cons_of_mem _ member)) others secondRemaining
              (fun value member => firstAvailable value (List.mem_cons_of_mem _ member))
              (fun value member => secondAvailable value (List.mem_cons_of_mem _ member))

/-- Strict source-member fusion derives exact physical Empty fusion after actual union filtering. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (ih : ∀ child ∈ expressions, Fusion child) : Fusion (.union expressions) := by
  intro Atom reader ready inputs firstNames secondNames firstOwn secondOwn firstMap secondMap
    firstBefore secondBefore firstRawHeap secondRawHeap firstRaw secondRaw firstFiltered secondFiltered left right
    firstContext secondContext aliases tests paired firstReplacements secondReplacements firstAvailable secondAvailable
    firstBuild secondBuild firstGrowth secondGrowth firstFilter secondFilter firstDone secondDone
  have parentBare := SourceCurrentUsedBinderOutputTags.bare (.union expressions) inputs firstNames secondNames firstOwn secondOwn
    firstBefore firstRawHeap secondBefore secondRawHeap firstContext.base secondContext.base
    firstRaw secondRaw firstBuild secondBuild tests
  obtain ⟨firstRaws,firstRawEntry,firstFilters,firstOutputs,firstMiddle,firstCut,firstFilterHeap,firstResult,firstFinal,
      firstMany,firstRawContext,firstMade,firstValues,firstCalls,firstParentFilter,firstParentDone,
      firstKept,firstCutKept,firstResultKept,firstCutAvailable,firstResultAvailable,firstMembersAvailable,firstFiltersAvailable,firstOutputsAvailable,
      firstParentWarm,firstParentStored,firstFiltersWarm,firstStoredWarm,firstSourceWarm,firstManyWarm,firstMadeWarm,firstSources⟩ :=
    SourceCurrentGeneratedUnionPreparation.prepare expressions _ firstBefore firstRawHeap reader firstContext firstRaw firstBuild
      ready firstGrowth firstAvailable firstOwn firstMap firstReplacements
  have firstWhole := firstKept.trans (firstCutKept.trans firstResultKept)
  obtain ⟨secondRaws,secondRawEntry,secondFilters,secondOutputs,secondMiddle,secondCut,secondFilterHeap,secondResult,secondFinal,
      secondMany,secondRawContext,secondMade,secondValues,secondCalls,secondParentFilter,secondParentDone,
      secondKept,secondCutKept,secondResultKept,secondCutAvailable,secondResultAvailable,secondMembersAvailable,secondFiltersAvailable,secondOutputsAvailable,
      secondParentWarm,secondParentStored,secondFiltersWarm,secondStoredWarm,secondSourceWarm,secondManyWarm,secondMadeWarm,secondSources⟩ :=
    SourceCurrentGeneratedUnionPreparation.prepare expressions _ secondBefore secondRawHeap firstFinal secondContext secondRaw secondBuild
      firstWhole.ready (grows_trans secondGrowth firstWhole.growth) (firstWhole.available secondRaw secondAvailable)
      secondOwn secondMap (fun name value found => firstWhole.available value (secondReplacements name value found))
  have secondWhole := secondKept.trans (secondCutKept.trans secondResultKept)
  have whole := firstWhole.trans secondWhole
  have finalReady := whole.ready
  have finalFirstReplacements : Replacements secondFinal firstMap := fun name value found =>
    whole.available value (firstReplacements name value found)
  have finalSecondReplacements : Replacements secondFinal secondMap := fun name value found =>
    whole.available value (secondReplacements name value found)
  have firstOldFilter : run (withoutSelfReference firstOwn firstRaw) secondFinal = (firstFiltered,secondFinal) := by
    simpa only [firstFilter] using (replay (withoutSelfReference firstOwn firstRaw) reader secondFinal
      ready.semantic.1.normal.facts.coherent.valid (by rw [firstFilter]; exact whole.growth))
  have secondOldFilter : run (withoutSelfReference secondOwn secondRaw) secondFinal = (secondFiltered,secondFinal) := by
    simpa only [secondFilter] using (replay (withoutSelfReference secondOwn secondRaw) reader secondFinal
      ready.semantic.1.normal.facts.coherent.valid (by rw [secondFilter]; exact whole.growth))
  have firstOldDone := InternedFreshOrdinaryStoredSubstitution.execute_replay firstFiltered firstMap reader secondFinal
    left reader ready.semantic.1.normal.facts.coherent.valid firstDone whole.growth
  have secondOldDone := InternedFreshOrdinaryStoredSubstitution.execute_replay secondFiltered secondMap reader secondFinal
    right reader ready.semantic.1.normal.facts.coherent.valid secondDone whole.growth
  have firstFinalMade := replay (makeUnion firstRaws) firstFinal secondFinal firstWhole.ready.semantic.1.normal.facts.coherent.valid
    (by rw [firstMadeWarm]; exact secondWhole.growth)
  have firstFinalFilter := filters_replay firstOwn firstFinal secondFinal firstWhole.ready.semantic.1.normal.facts.coherent.valid
    secondWhole.growth firstFiltersWarm
  have firstFinalStored := stored_replay firstMap firstFinal secondFinal firstWhole.ready.semantic.1.normal.facts.coherent.valid
    secondWhole.growth firstStoredWarm
  have firstMemberCalls := member_calls secondFinal firstOwn firstMap firstFinalFilter firstFinalStored
  have secondMemberCalls := member_calls secondFinal secondOwn secondMap secondFiltersWarm secondStoredWarm
  have firstFinalSource := source_extend expressions _ firstFinal secondFinal secondWhole.growth firstRaws firstSources
  have secondFinalSource := source_extend expressions _ secondFinal secondFinal (grows_refl _) secondRaws secondSources
  have childAliases : ∀ child ∈ expressions, Aliases child inputs firstNames secondNames := by
    intro child member a ha b hb
    exact aliases a (scope_subset expressions inputs child member a ha) b (scope_subset expressions inputs child member b hb)
  have childTests : ∀ child ∈ expressions, ∀ label ∈ Scope child inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn := by
    intro child member label found
    exact tests label (scope_subset expressions inputs child member label found)
  have matched := members_fusion expressions ih secondFinal finalReady inputs firstNames secondNames firstOwn secondOwn
    firstMap secondMap childAliases childTests paired finalFirstReplacements finalSecondReplacements firstRaws secondRaws
    firstFinalSource secondFinalSource
    (fun value member => secondWhole.available value (firstMembersAvailable value member)) secondMembersAvailable
  have firstCriterion := SourceCurrentFilteredUnionCoverage.empty_iff secondFinal finalReady firstRaws
    (fun value member => secondWhole.available value (firstMembersAvailable value member)) firstRaw firstFiltered left firstOwn firstMap
    (by simpa only [firstMadeWarm] using firstFinalMade) firstOldFilter finalFirstReplacements firstOldDone firstMemberCalls
  have secondCriterion := SourceCurrentFilteredUnionCoverage.empty_iff secondFinal finalReady secondRaws secondMembersAvailable
    secondRaw secondFiltered right secondOwn secondMap secondMadeWarm secondOldFilter finalSecondReplacements secondOldDone secondMemberCalls
  have equal : left.referenceOf = .empty ↔ right.referenceOf = .empty := by
    constructor
    · intro empty
      apply secondCriterion.mpr
      intro raw member retained cut output filterCall storedCall
      obtain ⟨original,included,bare,related⟩ := pair_right matched raw member
      obtain ⟨firstCut,firstOutput,firstFilterCall,firstStoredCall⟩ := firstMemberCalls original included
      have keep : original ≠ .reference firstOwn ∨ firstRaw = .reference firstOwn :=
        (or_congr (not_congr bare) parentBare).mpr retained
      have firstEmpty := firstCriterion.mp empty original included keep firstCut firstOutput firstFilterCall firstStoredCall
      have flags := related firstCut cut firstOutput output firstFilterCall filterCall firstStoredCall storedCall
      apply beq_iff_eq.mp
      rw [←flags]
      exact beq_iff_eq.mpr firstEmpty
    · intro empty
      apply firstCriterion.mpr
      intro raw member retained cut output filterCall storedCall
      obtain ⟨original,included,bare,related⟩ := pair_left matched raw member
      obtain ⟨secondCut,secondOutput,secondFilterCall,secondStoredCall⟩ := secondMemberCalls original included
      have keep : original ≠ .reference secondOwn ∨ secondRaw = .reference secondOwn :=
        (or_congr (not_congr bare) parentBare).mp retained
      have secondEmpty := secondCriterion.mp empty original included keep secondCut secondOutput secondFilterCall secondStoredCall
      have flags := related cut secondCut output secondOutput filterCall secondFilterCall storedCall secondStoredCall
      apply beq_iff_eq.mp
      rw [flags]
      exact beq_iff_eq.mpr secondEmpty
  exact Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using equal)

end MicroCFTA.SourceCurrentFilteredUnionFusion
