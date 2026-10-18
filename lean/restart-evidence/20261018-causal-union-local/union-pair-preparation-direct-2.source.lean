import MicroCFTA.SourceCurrentCausalUnionPreparation

/-!
# Two union schedules at one produced causal reader

Each side starts from its actual historical source call. Preparation runs
both sides in sequence. Actual retained effects replay the first schedule
at the joint final reader. The original parent values remain exact by
literal call determinism. No observation transport is used.
-/
namespace MicroCFTA.SourceCurrentCausalUnionPairPreparation
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (History)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Ordered actual member calls and original parent values share one final reader. -/
def Schedule (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (own : Reference) (environment : Environment Symbol Guard) (raw filtered result : Value Symbol Guard)
    (reader : State Symbol Guard) : Prop :=
  ∃ values filters outputs,
    Values reader values ∧ Values reader filters ∧ Values reader outputs ∧
    run (makeUnion values) reader = (raw,reader) ∧
    build (.union expressions) inputs reader = .done raw reader ∧
    buildMany expressions inputs reader = .done values reader ∧
    All₂ (fun raw cut => run (withoutSelfReference own raw) reader = (cut,reader)) values filters ∧
    All₂ (fun cut output => execute cut environment reader = .done output reader) filters outputs ∧
    All₂ (fun expression value => ∃ before after,
      Context before inputs ∧ build expression inputs before = .done value after ∧
      Grows after reader ∧ build expression inputs reader = .done value reader) expressions values ∧
    run (withoutSelfReference own raw) reader = (filtered,reader) ∧
    execute filtered environment reader = .done result reader

private theorem advance (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (own : Reference) (environment : Environment Symbol Guard) (raw filtered result : Value Symbol Guard)
    {before after : State Symbol Guard} (ready : Ready before) (kept : Keeps before after)
    (schedule : Schedule expressions inputs own environment raw filtered result before) :
    Schedule expressions inputs own environment raw filtered result after := by
  obtain ⟨values,filters,outputs,valuesAvailable,filtersAvailable,outputsAvailable,made,source,many,
    filterCalls,storedCalls,sources,parentFilter,parentDone⟩ := schedule
  have valid := ready.semantic.1.normal.facts.coherent.valid
  refine ⟨values,filters,outputs,
    (fun value member => kept.available value (valuesAvailable value member)),
    (fun value member => kept.available value (filtersAvailable value member)),
    (fun value member => kept.available value (outputsAvailable value member)),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [made] using InternedConstructorTemplates.replay (makeUnion values) before after valid
      (by simpa only [made] using kept.growth)
  · exact InternedFreshOrdinaryReplay.build_replay (.union expressions) inputs before after raw before
      valid source kept.growth
  · exact InternedFreshOrdinaryReplay.buildMany_replays expressions inputs before after values before
      valid many kept.growth
  · exact All₂.imp (fun raw cut actual => by
      simpa only [actual] using InternedConstructorTemplates.replay (withoutSelfReference own raw) before after valid
        (by simpa only [actual] using kept.growth)) filterCalls
  · exact All₂.imp (fun cut output actual =>
      InternedFreshOrdinaryStoredSubstitution.execute_replay cut environment before after output before
        valid actual kept.growth) storedCalls
  · apply All₂.imp _ sources
    intro expression value actual
    obtain ⟨start,returned,context,done,growth,warm⟩ := actual
    exact ⟨start,returned,context,done,grows_trans growth kept.growth,
      InternedFreshOrdinaryReplay.build_replay expression inputs before after value before valid warm kept.growth⟩
  · simpa only [parentFilter] using InternedConstructorTemplates.replay (withoutSelfReference own raw) before after valid
      (by simpa only [parentFilter] using kept.growth)
  · exact InternedFreshOrdinaryStoredSubstitution.execute_replay filtered environment before after result before
      valid parentDone kept.growth

private theorem parent_replay (own : Reference) (raw filtered result : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before after : State Symbol Guard)
    (ready : Ready before) (growth : Grows before after)
    (filter : run (withoutSelfReference own raw) before = (filtered,before))
    (done : execute filtered environment before = .done result before) :
    run (withoutSelfReference own raw) after = (filtered,after) ∧
      execute filtered environment after = .done result after := by
  have valid := ready.semantic.1.normal.facts.coherent.valid
  have filtered : run (withoutSelfReference own raw) after = (filtered,after) := by
    simpa only [filter] using InternedConstructorTemplates.replay (withoutSelfReference own raw)
      before after valid (by simpa only [filter] using growth)
  exact ⟨filtered,InternedFreshOrdinaryStoredSubstitution.execute_replay _ environment before after result before
    valid done growth⟩

private theorem parent_identity (own : Reference) (raw firstCut secondCut firstResult secondResult : Value Symbol Guard)
    (environment : Environment Symbol Guard) (reader : State Symbol Guard)
    (firstFilter : run (withoutSelfReference own raw) reader = (firstCut,reader))
    (secondFilter : run (withoutSelfReference own raw) reader = (secondCut,reader))
    (firstDone : execute firstCut environment reader = .done firstResult reader)
    (secondDone : execute secondCut environment reader = .done secondResult reader) :
    firstCut = secondCut ∧ firstResult = secondResult := by
  have cut : firstCut = secondCut := congrArg Prod.fst (firstFilter.symm.trans secondFilter)
  subst secondCut
  exact ⟨rfl,(Outcome.done.inj (firstDone.symm.trans secondDone)).1⟩

/-- Two actual parent endpoints acquire full member schedules at one produced causal reader. -/
theorem prepare (expressions : List (Syntax Symbol Guard))
    (firstInputs secondInputs : List (Value Symbol Guard))
    (firstBefore firstAfter secondBefore secondAfter reader : State Symbol Guard)
    (firstContext : Context firstBefore firstInputs) (secondContext : Context secondBefore secondInputs)
    (firstRaw secondRaw : Value Symbol Guard)
    (firstBuild : build (.union expressions) firstInputs firstBefore = .done firstRaw firstAfter)
    (secondBuild : build (.union expressions) secondInputs secondBefore = .done secondRaw secondAfter)
    (ready : Ready reader) (history : History empty reader)
    (firstGrowth : Grows firstAfter reader) (secondGrowth : Grows secondAfter reader)
    (firstAvailable : Available reader firstRaw) (secondAvailable : Available reader secondRaw)
    (firstOwn secondOwn : Reference) (firstMap secondMap : Environment Symbol Guard)
    (firstReplacements : Replacements reader firstMap) (secondReplacements : Replacements reader secondMap)
    (firstFiltered secondFiltered left right : Value Symbol Guard)
    (firstFilter : run (withoutSelfReference firstOwn firstRaw) reader = (firstFiltered,reader))
    (secondFilter : run (withoutSelfReference secondOwn secondRaw) reader = (secondFiltered,reader))
    (firstDone : execute firstFiltered firstMap reader = .done left reader)
    (secondDone : execute secondFiltered secondMap reader = .done right reader) :
    ∃ final, Keeps reader final ∧ Nonempty (History empty final) ∧
      Schedule expressions firstInputs firstOwn firstMap firstRaw firstFiltered left final ∧
      Schedule expressions secondInputs secondOwn secondMap secondRaw secondFiltered right final := by
  obtain ⟨firstValues,firstRawHeap,firstFilters,firstOutputs,firstMiddle,firstCut,firstFilterHeap,firstResult,middle,
    _firstMany,_firstContext,_firstMade,_firstValues,firstCalls,_firstParentFilter,_firstParentDone,
    firstMembers,firstParent,firstStored,_firstCutAvailable,_firstResultAvailable,
    firstFinalValues,firstFinalFilters,firstFinalOutputs,firstParentWarm,firstParentStored,
    firstFiltersWarm,firstStoredWarm,firstSourceWarm,firstManyWarm,firstMadeWarm,firstSources,
    _firstMemberHistory,_firstFilterHistory,_firstStoredHistory,⟨middleHistory⟩⟩ :=
    SourceCurrentCausalUnionPreparation.prepare expressions firstInputs firstBefore firstAfter reader firstContext
      firstRaw firstBuild ready history firstGrowth firstAvailable firstOwn firstMap firstReplacements
  have firstKept := firstMembers.trans (firstParent.trans firstStored)
  obtain ⟨firstKnownFilter,firstKnownDone⟩ := parent_replay firstOwn firstRaw firstFiltered left firstMap reader middle
    ready firstKept.growth firstFilter firstDone
  obtain ⟨rfl,rfl⟩ := parent_identity firstOwn firstRaw firstCut firstFiltered firstResult left firstMap middle
    firstParentWarm firstKnownFilter firstParentStored firstKnownDone
  have firstSchedule : Schedule expressions firstInputs firstOwn firstMap firstRaw firstCut firstResult middle :=
    ⟨firstValues,firstFilters,firstOutputs,firstFinalValues,firstFinalFilters,firstFinalOutputs,firstMadeWarm,
      firstSourceWarm,firstManyWarm,firstFiltersWarm,firstStoredWarm,firstSources,firstParentWarm,firstParentStored⟩
  obtain ⟨secondValues,secondRawHeap,secondFilters,secondOutputs,secondMiddle,secondCut,secondFilterHeap,secondResult,final,
    _secondMany,_secondContext,_secondMade,_secondValues,secondCalls,_secondParentFilter,_secondParentDone,
    secondMembers,secondParent,secondStored,_secondCutAvailable,_secondResultAvailable,
    secondFinalValues,secondFinalFilters,secondFinalOutputs,secondParentWarm,secondParentStored,
    secondFiltersWarm,secondStoredWarm,secondSourceWarm,secondManyWarm,secondMadeWarm,secondSources,
    _secondMemberHistory,_secondFilterHistory,_secondStoredHistory,finalHistory⟩ :=
    SourceCurrentCausalUnionPreparation.prepare expressions secondInputs secondBefore secondAfter middle secondContext
      secondRaw secondBuild firstKept.ready middleHistory (grows_trans secondGrowth firstKept.growth)
      (firstKept.available secondRaw secondAvailable) secondOwn secondMap
      (fun name value found => firstKept.available value (secondReplacements name value found))
  have secondKept := secondMembers.trans (secondParent.trans secondStored)
  have whole := firstKept.trans secondKept
  obtain ⟨secondKnownFilter,secondKnownDone⟩ := parent_replay secondOwn secondRaw secondFiltered right secondMap reader final
    ready whole.growth secondFilter secondDone
  obtain ⟨rfl,rfl⟩ := parent_identity secondOwn secondRaw secondCut secondFiltered secondResult right secondMap final
    secondParentWarm secondKnownFilter secondParentStored secondKnownDone
  have secondSchedule : Schedule expressions secondInputs secondOwn secondMap secondRaw secondCut secondResult final :=
    ⟨secondValues,secondFilters,secondOutputs,secondFinalValues,secondFinalFilters,secondFinalOutputs,secondMadeWarm,
      secondSourceWarm,secondManyWarm,secondFiltersWarm,secondStoredWarm,secondSources,secondParentWarm,secondParentStored⟩
  exact ⟨final,whole,finalHistory,
    advance expressions firstInputs firstOwn firstMap firstRaw firstCut firstResult firstKept.ready secondKept firstSchedule,
    secondSchedule⟩

end MicroCFTA.SourceCurrentCausalUnionPairPreparation
