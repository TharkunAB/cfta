import MicroCFTA.SourceCurrentTrackedFilteredFusion
import MicroCFTA.SourceCurrentSourceChildDepth
import MicroCFTA.SourceCurrentFilteredUnionCoverage
import MicroCFTA.SourceCurrentUsedBinderOutputTags

/-!
# Tracked root profiles through actual filtered source unions

Original member depths use the same bound as the parent. Two finite
preparations retain the historical source calls and warm reader calls.
Exact literal parts determine opacity and tracked root references.
-/
namespace MicroCFTA.SourceCurrentTrackedFilteredUnionFusion
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
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
open SourceCurrentTrackedFilteredFusion (Fusion)
open SourceCurrentTrackedRootProfile (mask observe Related)
open SourceCurrentLiteralRootParts (Literal Row)
open InternedRootProfile (Profile profile many combine Equivalent)
open InternedStoredMuOrigins (Normal)

private theorem many_nonopaque (markers : List Reference) (values : List (Value Symbol Guard)) :
    mask markers (many values) ≠ none ↔ ∀ value ∈ values, observe markers value ≠ none := by
  induction values with
  | nil => simp [many,mask]
  | cons first rest ih =>
      rw [many,SourceCurrentTrackedRootProfile.mask_combine]
      change combine (observe markers first) (mask markers (many rest)) ≠ none ↔ _
      cases one : observe markers first <;> cases two : mask markers (many rest) <;>
        simp_all [combine]

private theorem many_names (markers : List Reference) (values : List (Value Symbol Guard))
    (pure : mask markers (many values) ≠ none) (name : Reference) :
    name ∈ (mask markers (many values)).getD [] ↔
      ∃ value ∈ values, name ∈ (observe markers value).getD [] := by
  induction values with
  | nil => simp [many,mask]
  | cons first rest ih =>
      have members := (many_nonopaque markers (first::rest)).mp pure
      have one := members first List.mem_cons_self
      have tail := (many_nonopaque markers rest).mpr (fun value found => members value (List.mem_cons_of_mem _ found))
      have names := ih tail
      rw [many,SourceCurrentTrackedRootProfile.mask_combine]
      change name ∈ (combine (observe markers first) (mask markers (many rest))).getD [] ↔ _
      cases firstProfile : observe markers first with
      | none => exact False.elim (one firstProfile)
      | some firstNames =>
          cases restProfile : mask markers (many rest) with
          | none => exact False.elim (tail restProfile)
          | some restNames =>
              rw [restProfile] at names
              change name ∈ (combine (some firstNames) (some restNames)).getD [] ↔ _
              simpa only [combine,Option.getD_some,List.mem_append,List.mem_cons,exists_eq_or_imp,firstProfile,
                Option.getD_some] using or_congr Iff.rfl names

private def PureParts (markers : List Reference) (value : Value Symbol Guard) : Prop :=
  (∀ row, ¬ Row value row) ∧ ∀ atom, Literal value atom → ∃ name, atom = .reference name ∧ name ∈ markers

private theorem nonopaque_parts (markers : List Reference) (reader : State Symbol Guard) (normal : Normal reader)
    (value : Value Symbol Guard) (available : Available reader value) :
    observe markers value ≠ none ↔ PureParts markers value := by
  cases value with
  | empty =>
      constructor
      · intro _
        constructor
        · intro row found; cases found
        · intro atom found; cases found
      · intro _; simp [observe,profile,mask]
  | reference own =>
      have observed : observe markers (.reference own : Value Symbol Guard) ≠ none ↔ own ∈ markers := by
        simp [observe,profile,mask]
      rw [observed]
      constructor
      · intro tracked
        constructor
        · intro row found; cases found
        · intro atom found; cases found; exact ⟨own,rfl,tracked⟩
      · intro parts; obtain ⟨name,same,tracked⟩ := parts.2 _ (.reference own); cases same; exact tracked
  | mu entry body depth ordinary =>
      constructor
      · intro impossible; exact False.elim (impossible (by simp [observe,profile,mask]))
      · intro parts
        obtain ⟨name,impossible,_⟩ := parts.2 _ (.mu entry body depth ordinary)
        cases impossible
  | node entry rows level free =>
      constructor
      · intro impossible; exact False.elim (impossible (by simp [observe,profile,mask]))
      · intro parts
        have proper := InternedNonemptyRecords.resident_nonempty reader normal.proper _ available.resident
        obtain ⟨row,member⟩ := List.exists_mem_of_ne_nil rows proper
        exact False.elim (parts.1 row (.node member))
  | union entry members level free =>
      rw [observe,profile,many_nonopaque]
      constructor
      · intro pure
        constructor
        · intro row found
          obtain ⟨child,member,part⟩ := (SourceCurrentLiteralRootParts.row_union _ _ _ _ _).mp found
          exact ((nonopaque_parts markers reader normal child (available.children child member)).mp (pure child member)).1 row part
        · intro atom found
          obtain ⟨child,member,part⟩ := (SourceCurrentLiteralRootParts.literal_union _ _ _ _ _).mp found
          exact ((nonopaque_parts markers reader normal child (available.children child member)).mp (pure child member)).2 atom part
      · intro parts child member
        apply (nonopaque_parts markers reader normal child (available.children child member)).mpr
        exact ⟨fun row found => parts.1 row (.union member found),fun atom found => parts.2 atom (.union member found)⟩
termination_by sizeOf value
decreasing_by all_goals have smaller := List.sizeOf_lt_of_mem member; simp_wf; simp_all; omega

private theorem reference_names (markers : List Reference) (reader : State Symbol Guard) (normal : Normal reader)
    (value : Value Symbol Guard) (available : Available reader value)
    (pure : observe markers value ≠ none) (name : Reference) :
    name ∈ (observe markers value).getD [] ↔ Literal value (.reference name) := by
  cases value with
  | empty =>
      simp only [observe,profile,mask,List.all_nil,↓reduceIte,Option.getD_some,List.not_mem_nil,false_iff]
      intro impossible; cases impossible
  | reference own =>
      have tracked := (nonopaque_parts markers reader normal (.reference own) available).mp pure
      obtain ⟨other,same,present⟩ := tracked.2 _ (.reference own)
      cases same
      simp only [observe,profile,mask,List.all_cons,List.all_nil,Bool.and_true,List.contains_eq_mem,
        decide_eq_true_eq,present,↓reduceIte,Option.getD_some,List.mem_singleton]
      constructor
      · intro same; subst name; exact .reference _
      · intro found; cases found; rfl
  | node | mu => exact False.elim (pure (by simp [observe,profile,mask]))
  | union entry members level free =>
      have combined : mask markers (many members) ≠ none := by simpa only [observe,profile] using pure
      rw [observe,profile,many_names markers members combined]
      rw [SourceCurrentLiteralRootParts.literal_union]
      apply exists_congr
      intro child
      apply and_congr_right
      intro member
      exact reference_names markers reader normal child (available.children child member)
        ((many_nonopaque markers members).mp combined child member) name
termination_by sizeOf value
decreasing_by have smaller := List.sizeOf_lt_of_mem member; simp_wf; simp_all; omega


private theorem filtered_available [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard) (ready : Ready reader)
    (own : Reference) (raw filtered : Value Symbol Guard) (available : Available reader raw)
    (actual : run (withoutSelfReference own raw) reader = (filtered,reader)) : Available reader filtered := by
  apply (InternedNestedFacts.filter_verified own raw reader ready.semantic.1.normal.facts available).result filtered reader
  simp only [work,actual]

private theorem output_available [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard) (ready : Ready reader)
    (raw result : Value Symbol Guard) (environment : Environment Symbol Guard)
    (available : Available reader raw) (replacements : Replacements reader environment)
    (actual : execute raw environment reader = .done result reader) : Available reader result :=
  (InternedFreshOrdinaryFacts.build_verified _ _ reader ready.semantic.1.normal.facts
    (InternedStoredSubstitution.inputs_available raw environment reader available replacements)).result result reader actual

private theorem coverage_nonopaque [DecidableEq (EdgeKey Symbol Guard)]
    (markers : List Reference) (reader : State Symbol Guard) (ready : Ready reader)
    (values : List (Value Symbol Guard)) (available : Values reader values)
    (parent filtered result : Value Symbol Guard) (own : Reference) (environment : Environment Symbol Guard)
    (resultAvailable : Available reader result)
    (made : run (makeUnion values) reader = (parent,reader))
    (parentFilter : run (withoutSelfReference own parent) reader = (filtered,reader))
    (replacements : Replacements reader environment)
    (called : execute filtered environment reader = .done result reader)
    (members : ∀ raw ∈ values, ∃ cut output,
      run (withoutSelfReference own raw) reader = (cut,reader) ∧
      execute cut environment reader = .done output reader) :
    observe markers result ≠ none ↔ ∀ raw ∈ values, (raw ≠ .reference own ∨ parent = .reference own) →
      ∀ cut output, run (withoutSelfReference own raw) reader = (cut,reader) →
      execute cut environment reader = .done output reader → observe markers output ≠ none := by
  have parts := SourceCurrentFilteredUnionCoverage.parts reader ready values available parent filtered result own environment
    made parentFilter replacements called members
  rw [nonopaque_parts markers reader ready.semantic.1.normal result resultAvailable]
  constructor
  · intro pure raw member retained cut output filterCall storedCall
    have outputAvailable := output_available reader ready cut output environment
      (filtered_available reader ready own raw cut (available raw member) filterCall) replacements storedCall
    apply (nonopaque_parts markers reader ready.semantic.1.normal output outputAvailable).mpr
    constructor
    · intro row found
      exact pure.1 row ((parts.2 row).mpr ⟨raw,member,retained,cut,output,filterCall,storedCall,found⟩)
    · intro atom found
      exact pure.2 atom ((parts.1 atom).mpr ⟨raw,member,retained,cut,output,filterCall,storedCall,found⟩)
  · intro membersPure
    constructor
    · intro row found
      obtain ⟨raw,member,retained,cut,output,filterCall,storedCall,inside⟩ := (parts.2 row).mp found
      have outputAvailable := output_available reader ready cut output environment
        (filtered_available reader ready own raw cut (available raw member) filterCall) replacements storedCall
      exact ((nonopaque_parts markers reader ready.semantic.1.normal output outputAvailable).mp
        (membersPure raw member retained cut output filterCall storedCall)).1 row inside
    · intro atom found
      obtain ⟨raw,member,retained,cut,output,filterCall,storedCall,inside⟩ := (parts.1 atom).mp found
      have outputAvailable := output_available reader ready cut output environment
        (filtered_available reader ready own raw cut (available raw member) filterCall) replacements storedCall
      exact ((nonopaque_parts markers reader ready.semantic.1.normal output outputAvailable).mp
        (membersPure raw member retained cut output filterCall storedCall)).2 atom inside

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
    (markers : List Reference) (bound : Nat) (expressions : List (Syntax Symbol Guard)) (ih : ∀ child ∈ expressions, Fusion bound child)
    (reader : State Symbol Guard) (ready : Ready reader)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (firstOwn secondOwn : Reference) (firstMap secondMap : Environment Symbol Guard)
    (aliases : ∀ child ∈ expressions, Aliases child inputs firstNames secondNames)
    (tests : ∀ child ∈ expressions, ∀ label ∈ Scope child inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn)
    (paired : SourceCurrentReaderReplacementSlots.Paired
      (Related markers) firstMap secondMap
      (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader firstMap) (secondReplacements : Replacements reader secondMap)
    (firstRaws secondRaws : List (Value Symbol Guard))
    (firstSource : All₂ (fun child raw => SourceCall child (inputs.map (input firstNames)) reader raw) expressions firstRaws)
    (secondSource : All₂ (fun child raw => SourceCall child (inputs.map (input secondNames)) reader raw) expressions secondRaws)
    (firstAvailable : Values reader firstRaws) (secondAvailable : Values reader secondRaws)
    (firstBounds : ∀ raw ∈ firstRaws, raw.depth ≤ bound) (secondBounds : ∀ raw ∈ secondRaws, raw.depth ≤ bound) :
    All₂ (fun a b => (a = .reference firstOwn ↔ b = .reference secondOwn) ∧
      ∀ firstFiltered secondFiltered left right,
        run (withoutSelfReference firstOwn a) reader = (firstFiltered,reader) →
        run (withoutSelfReference secondOwn b) reader = (secondFiltered,reader) →
        execute firstFiltered firstMap reader = .done left reader →
        execute secondFiltered secondMap reader = .done right reader →
        Related markers left right) firstRaws secondRaws := by
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
            exact ih expression List.mem_cons_self markers reader ready inputs firstNames secondNames firstOwn secondOwn firstMap secondMap
              before later after final raw other firstFiltered secondFiltered left right
              (firstBounds raw List.mem_cons_self) (secondBounds other List.mem_cons_self) firstContext secondContext
              (aliases expression List.mem_cons_self) (tests expression List.mem_cons_self) paired firstReplacements secondReplacements
              (firstAvailable raw List.mem_cons_self) (secondAvailable other List.mem_cons_self)
              firstBuild secondBuild firstGrowth secondGrowth firstFilter secondFilter firstDone secondDone
          · exact induct (fun child member => ih child (List.mem_cons_of_mem _ member))
              (fun child member => aliases child (List.mem_cons_of_mem _ member))
              (fun child member => tests child (List.mem_cons_of_mem _ member)) others secondRemaining
              (fun value member => firstAvailable value (List.mem_cons_of_mem _ member))
              (fun value member => secondAvailable value (List.mem_cons_of_mem _ member))
              (fun value member => firstBounds value (List.mem_cons_of_mem _ member))
              (fun value member => secondBounds value (List.mem_cons_of_mem _ member))

/-- Strict member laws at one original depth bound derive the actual filtered union law at that same bound. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (bound : Nat) (expressions : List (Syntax Symbol Guard))
    (ih : ∀ child ∈ expressions, Fusion bound child) : Fusion bound (.union expressions) := by
  intro markers Atom reader ready inputs firstNames secondNames firstOwn secondOwn firstMap secondMap
    firstBefore secondBefore firstRawHeap secondRawHeap firstRaw secondRaw firstFiltered secondFiltered left right
    firstDepth secondDepth firstContext secondContext aliases tests paired firstReplacements secondReplacements firstAvailable secondAvailable
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
  obtain ⟨firstOriginals,firstOriginalHeap,firstOriginalMany,_firstOriginalMade,_firstOriginalContext,firstOriginalBounds⟩ :=
    SourceCurrentSourceChildDepth.union expressions _ firstBefore firstRawHeap firstContext firstRaw firstBuild
  have firstOriginalSame := (Outcome.done.inj (firstOriginalMany.symm.trans firstMany)).1
  rw [firstOriginalSame] at firstOriginalBounds
  obtain ⟨secondOriginals,secondOriginalHeap,secondOriginalMany,_secondOriginalMade,_secondOriginalContext,secondOriginalBounds⟩ :=
    SourceCurrentSourceChildDepth.union expressions _ secondBefore secondRawHeap secondContext secondRaw secondBuild
  have secondOriginalSame := (Outcome.done.inj (secondOriginalMany.symm.trans secondMany)).1
  rw [secondOriginalSame] at secondOriginalBounds
  have childAliases : ∀ child ∈ expressions, Aliases child inputs firstNames secondNames := by
    intro child member a ha b hb
    exact aliases a (scope_subset expressions inputs child member a ha) b (scope_subset expressions inputs child member b hb)
  have childTests : ∀ child ∈ expressions, ∀ label ∈ Scope child inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn := by
    intro child member label found
    exact tests label (scope_subset expressions inputs child member label found)
  have matched := members_fusion markers bound expressions ih secondFinal finalReady inputs firstNames secondNames firstOwn secondOwn
    firstMap secondMap childAliases childTests paired finalFirstReplacements finalSecondReplacements firstRaws secondRaws
    firstFinalSource secondFinalSource
    (fun value member => secondWhole.available value (firstMembersAvailable value member)) secondMembersAvailable
    (fun value member => Nat.le_trans (firstOriginalBounds value member) firstDepth)
    (fun value member => Nat.le_trans (secondOriginalBounds value member) secondDepth)
  have firstFinalAvailable : Values secondFinal firstRaws := fun value member =>
    secondWhole.available value (firstMembersAvailable value member)
  have leftAvailable := output_available secondFinal finalReady firstFiltered left firstMap
    (whole.available firstFiltered (filtered_available reader ready firstOwn firstRaw firstFiltered firstAvailable firstFilter))
    finalFirstReplacements firstOldDone
  have rightAvailable := output_available secondFinal finalReady secondFiltered right secondMap
    (whole.available secondFiltered (filtered_available reader ready secondOwn secondRaw secondFiltered secondAvailable secondFilter))
    finalSecondReplacements secondOldDone
  have firstMadeFinal : run (makeUnion firstRaws) secondFinal = (firstRaw,secondFinal) := by
    simpa only [firstMadeWarm] using firstFinalMade
  have firstCriterion := coverage_nonopaque markers secondFinal finalReady firstRaws firstFinalAvailable
    firstRaw firstFiltered left firstOwn firstMap leftAvailable firstMadeFinal firstOldFilter
    finalFirstReplacements firstOldDone firstMemberCalls
  have secondCriterion := coverage_nonopaque markers secondFinal finalReady secondRaws secondMembersAvailable
    secondRaw secondFiltered right secondOwn secondMap rightAvailable secondMadeWarm secondOldFilter
    finalSecondReplacements secondOldDone secondMemberCalls
  have equalPure : observe markers left ≠ none ↔ observe markers right ≠ none := by
    constructor
    · intro pure
      apply secondCriterion.mpr
      intro raw member retained cut output filterCall storedCall
      obtain ⟨original,included,bare,related⟩ := pair_right matched raw member
      obtain ⟨firstCut,firstOutput,firstFilterCall,firstStoredCall⟩ := firstMemberCalls original included
      have keep : original ≠ .reference firstOwn ∨ firstRaw = .reference firstOwn :=
        (or_congr (not_congr bare) parentBare).mpr retained
      have firstPure := firstCriterion.mp pure original included keep firstCut firstOutput firstFilterCall firstStoredCall
      exact fun opaque => firstPure ((related firstCut cut firstOutput output firstFilterCall filterCall firstStoredCall storedCall).1.mpr opaque)
    · intro pure
      apply firstCriterion.mpr
      intro raw member retained cut output filterCall storedCall
      obtain ⟨original,included,bare,related⟩ := pair_left matched raw member
      obtain ⟨secondCut,secondOutput,secondFilterCall,secondStoredCall⟩ := secondMemberCalls original included
      have keep : original ≠ .reference secondOwn ∨ secondRaw = .reference secondOwn :=
        (or_congr (not_congr bare) parentBare).mp retained
      have secondPure := secondCriterion.mp pure original included keep secondCut secondOutput secondFilterCall secondStoredCall
      exact fun opaque => secondPure ((related cut secondCut output secondOutput filterCall secondFilterCall storedCall secondStoredCall).1.mp opaque)
  have firstParts := SourceCurrentFilteredUnionCoverage.parts secondFinal finalReady firstRaws firstFinalAvailable
    firstRaw firstFiltered left firstOwn firstMap firstMadeFinal firstOldFilter finalFirstReplacements firstOldDone firstMemberCalls
  have secondParts := SourceCurrentFilteredUnionCoverage.parts secondFinal finalReady secondRaws secondMembersAvailable
    secondRaw secondFiltered right secondOwn secondMap secondMadeWarm secondOldFilter finalSecondReplacements secondOldDone secondMemberCalls
  refine ⟨not_iff_not.mp equalPure,?_⟩
  intro name
  by_cases leftPure : observe markers left = none
  · have rightOpaque := (not_iff_not.mp equalPure).mp leftPure
    simp [leftPure,rightOpaque]
  · have rightPure := equalPure.mp leftPure
    rw [reference_names markers secondFinal finalReady.semantic.1.normal left leftAvailable leftPure,
      reference_names markers secondFinal finalReady.semantic.1.normal right rightAvailable rightPure]
    constructor
    · intro found
      obtain ⟨raw,member,retained,cut,output,filterCall,storedCall,inside⟩ := (firstParts.1 _).mp found
      obtain ⟨other,included,bare,related⟩ := pair_left matched raw member
      obtain ⟨secondCut,secondOutput,secondFilterCall,secondStoredCall⟩ := secondMemberCalls other included
      have pure := firstCriterion.mp leftPure raw member retained cut output filterCall storedCall
      have firstOutputAvailable := output_available secondFinal finalReady cut output firstMap
        (filtered_available secondFinal finalReady firstOwn raw cut (firstFinalAvailable raw member) filterCall)
        finalFirstReplacements storedCall
      have secondOutputAvailable := output_available secondFinal finalReady secondCut secondOutput secondMap
        (filtered_available secondFinal finalReady secondOwn other secondCut (secondMembersAvailable other included) secondFilterCall)
        finalSecondReplacements secondStoredCall
      have same := related cut secondCut output secondOutput filterCall secondFilterCall storedCall secondStoredCall
      have otherPure : observe markers secondOutput ≠ none := fun opaque => pure (same.1.mpr opaque)
      have names := (reference_names markers secondFinal finalReady.semantic.1.normal output firstOutputAvailable pure name).mpr inside
      have otherNames := (same.2 name).mp names
      apply (secondParts.1 _).mpr
      exact ⟨other,included,(or_congr (not_congr bare) parentBare).mp retained,secondCut,secondOutput,secondFilterCall,secondStoredCall,
        (reference_names markers secondFinal finalReady.semantic.1.normal secondOutput secondOutputAvailable otherPure name).mp otherNames⟩
    · intro found
      obtain ⟨raw,member,retained,cut,output,filterCall,storedCall,inside⟩ := (secondParts.1 _).mp found
      obtain ⟨other,included,bare,related⟩ := pair_right matched raw member
      obtain ⟨firstCut,firstOutput,firstFilterCall,firstStoredCall⟩ := firstMemberCalls other included
      have pure := secondCriterion.mp rightPure raw member retained cut output filterCall storedCall
      have secondOutputAvailable := output_available secondFinal finalReady cut output secondMap
        (filtered_available secondFinal finalReady secondOwn raw cut (secondMembersAvailable raw member) filterCall)
        finalSecondReplacements storedCall
      have firstOutputAvailable := output_available secondFinal finalReady firstCut firstOutput firstMap
        (filtered_available secondFinal finalReady firstOwn other firstCut (firstFinalAvailable other included) firstFilterCall)
        finalFirstReplacements firstStoredCall
      have same := related firstCut cut firstOutput output firstFilterCall filterCall firstStoredCall storedCall
      have otherPure : observe markers firstOutput ≠ none := fun opaque => pure (same.1.mp opaque)
      have names := (reference_names markers secondFinal finalReady.semantic.1.normal output secondOutputAvailable pure name).mpr inside
      have otherNames := (same.2 name).mpr names
      apply (firstParts.1 _).mpr
      exact ⟨other,included,(or_congr (not_congr bare) parentBare).mpr retained,firstCut,firstOutput,firstFilterCall,firstStoredCall,
        (reference_names markers secondFinal finalReady.semantic.1.normal firstOutput firstOutputAvailable otherPure name).mp otherNames⟩

end MicroCFTA.SourceCurrentTrackedFilteredUnionFusion
