import MicroCFTA.SourceCurrentFiniteObservationExecution
import MicroCFTA.SourceCurrentStoredUnionSurvival

/-!
# Finite source union reconstruction at one observation reader

The execution heap can grow while the observation reader stays fixed.
Strict indexed member hypotheses apply at every actual execution heap.
Both member schedules are completed and replayed at their common final
heap. Uniform union fusion retains the original finite observation reader.
No observation relation is transported along heap growth. Source members
can contain arbitrary nested Mu syntax. The binder case remains separate.
-/
namespace MicroCFTA.SourceCurrentReaderFiniteUnionStep
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt)
open SourceCurrentOpenObservations (Same)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentReaderReplacementSlots (Paired)
open SourceCurrentFiniteObservationExecution (AlignedAt)
open Language
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem source_children (expressions : List (Syntax Symbol Guard))
    (inputs : List (Value Symbol Guard)) (common : State Symbol Guard) (valid : Valid common)
    (outputs : List (Value Symbol Guard))
    (actual : buildMany expressions inputs common = .done outputs common) :
    All₂ (fun expression output => build expression inputs common = .done output common) expressions outputs := by
  induction expressions generalizing outputs with
  | nil =>
      simp only [buildMany,Outcome.done.injEq] at actual
      obtain ⟨rfl,_⟩ := actual
      exact .nil
  | cons expression rest ih =>
      cases called : build expression inputs common with
      | pending key state => simp only [buildMany,called,Outcome.bind] at actual; cases actual
      | done output middle =>
          cases tail : buildMany rest inputs middle with
          | pending key state => simp only [buildMany,called,tail,Outcome.bind] at actual; cases actual
          | done remaining final =>
              simp only [buildMany,called,tail,Outcome.bind,Outcome.done.injEq] at actual
              obtain ⟨rfl,sameHeap⟩ := actual
              rw [sameHeap] at tail
              have middleValid : Valid middle := by
                simpa only [called,Outcome.state] using
                  (InternedFreshOrdinaryGrowth.build_correct expression inputs common valid).1
              have growth : Grows middle common := by
                simpa only [tail,Outcome.state] using
                  (InternedFreshOrdinaryGrowth.buildMany_correct rest inputs middle middleValid).2
              have head := InternedFreshOrdinaryReplay.build_replay expression inputs common common output middle valid called growth
              have rest := InternedFreshOrdinaryReplay.buildMany_replays rest inputs middle common remaining common
                middleValid tail (grows_refl _)
              exact .cons head (ih remaining rest)

private theorem children_aligned (expressions : List (Syntax Symbol Guard))
    (depth : Nat) (view common : State Symbol Guard)
    (cases : ∀ expression ∈ expressions, AlignedAt depth view common expression)
    (leftInputs rightInputs : List (Value Symbol Guard))
    (first second : Environment Symbol Guard) (paired : Paired (RelatedAt depth view) first second leftInputs rightInputs)
    (ready : Ready common)
    (firstInputs : Values common leftInputs)
    (secondInputs : Values common rightInputs)
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second)
    (rawFirst rawSecond left right : List (Value Symbol Guard))
    (firstRaw : buildMany expressions leftInputs common = .done rawFirst common)
    (secondRaw : buildMany expressions rightInputs common = .done rawSecond common)
    (firstDone : All₂ (fun raw output => execute raw first common = .done output common) rawFirst left)
    (secondDone : All₂ (fun raw output => execute raw second common = .done output common) rawSecond right) :
    All₂ (RelatedAt depth view) left right := by
  have firstSource := source_children expressions _ common ready.semantic.1.normal.facts.coherent.valid rawFirst firstRaw
  have secondSource := source_children expressions _ common ready.semantic.1.normal.facts.coherent.valid rawSecond secondRaw
  have firstWarm := firstDone
  have secondWarm := secondDone
  clear firstRaw secondRaw firstDone secondDone
  induction firstSource generalizing rawSecond left right with
  | nil => cases secondSource; cases firstWarm; cases secondWarm; exact .nil
  | @cons expression raw expressions raws firstRaw remaining ih =>
      cases secondSource with
      | cons secondRaw secondRemaining =>
          cases firstWarm with
          | cons firstDone firstRest =>
              cases secondWarm with
              | cons secondDone secondRest =>
                  exact .cons (cases expression List.mem_cons_self leftInputs rightInputs first second paired
                    ready firstInputs secondInputs firstReplacements secondReplacements _ _ firstRaw secondRaw
                    _ _ firstDone secondDone)
                    (ih (fun expression member => cases expression (List.mem_cons_of_mem _ member))
                      _ _ _ secondRemaining firstRest secondRest)

private theorem raw_parts (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (common : State Symbol Guard) (context : Context common inputs) (result : Value Symbol Guard)
    (actual : build (.union expressions) inputs common = .done result common) :
    ∃ values, buildMany expressions inputs common = .done values common ∧
      Values common values ∧ run (makeUnion values) common = (result,common) := by
  cases called : buildMany expressions inputs common with
  | pending key state => simp only [build,called,Outcome.bind] at actual; cases actual
  | done values middle =>
      have made : run (makeUnion values) middle = (result,common) :=
        Prod.ext (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).1
          (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).2
      have checked := InternedFreshOrdinaryFacts.buildMany_verified expressions inputs common context.normal.facts context.inputs
      have middleFacts : InternedNestedFacts.Facts middle := by simpa only [called,Outcome.state] using checked.facts
      have growth : Grows middle common := by
        simpa only [made] using (run_correct (makeUnion values) middle middleFacts.coherent.valid).2
      have repeated := InternedConstructorTemplates.replay (makeUnion values) middle common middleFacts.coherent.valid
        (by rw [made]; exact grows_refl _)
      rw [made] at repeated
      have warm := InternedFreshOrdinaryReplay.buildMany_replays expressions inputs common common values middle
        context.normal.facts.coherent.valid called growth
      have available := (InternedFreshOrdinaryFacts.buildMany_verified expressions inputs common
        context.normal.facts context.inputs).result values common warm
      exact ⟨values,by simpa only [called] using warm,available,repeated⟩

private theorem all_empty {depth : Nat} {view : State Symbol Guard} {first second : List (Value Symbol Guard)} (paired : All₂ (RelatedAt depth view) first second) :
    (∀ value ∈ first, value.referenceOf = .empty) ↔ ∀ value ∈ second, value.referenceOf = .empty := by
  induction paired with
  | nil => exact Iff.rfl
  | cons head tail ih =>
      constructor
      · intro all value member
        rcases List.mem_cons.mp member with rfl | later
        · exact head.1.mp (all _ List.mem_cons_self)
        · exact ih.mp (fun value member => all value (List.mem_cons_of_mem _ member)) value later
      · intro all value member
        rcases List.mem_cons.mp member with rfl | later
        · exact head.1.mpr (all _ List.mem_cons_self)
        · exact ih.mpr (fun value member => all value (List.mem_cons_of_mem _ member)) value later

private theorem list_same {depth : Nat} {view : State Symbol Guard}
    {first second : List (Value Symbol Guard)} (paired : All₂ (RelatedAt depth view) first second) :
    Same depth view first second := by
  induction paired with
  | nil => exact Same.refl depth view []
  | @cons first second rest remaining head tail ih =>
      simpa only [List.singleton_append] using
        SourceCurrentOpenObservationLists.append depth view [first] [second] rest remaining head.2 ih

/-- Strict members at every execution heap derive union agreement at the fixed observation reader. -/
theorem union (expressions : List (Syntax Symbol Guard)) (depth : Nat) (view : State Symbol Guard)
    (children : ∀ (index : Nat) (child : Syntax Symbol Guard), expressions[index]? = some child →
      sizeOf child < sizeOf (.union expressions : Syntax Symbol Guard) →
      ∀ executionReader, AlignedAt depth view executionReader child)
    (common : State Symbol Guard) : AlignedAt depth view common (.union expressions) := by
  intro leftInputs rightInputs first second paired ready firstInputs secondInputs
    firstReplacements secondReplacements rawFirst rawSecond firstRaw secondRaw result other firstDone secondDone
  have firstContext : Context common leftInputs :=
    ⟨ready.semantic.1.normal,firstInputs,ready.semantic.1.profiles,ready.semantic.1.freeNames⟩
  have secondContext : Context common rightInputs :=
    ⟨ready.semantic.1.normal,secondInputs,ready.semantic.1.profiles,ready.semantic.1.freeNames⟩
  obtain ⟨rawFirsts,firstMany,firstAvailable,firstMade⟩ := raw_parts expressions leftInputs common firstContext rawFirst firstRaw
  obtain ⟨rawSeconds,secondMany,secondAvailable,secondMade⟩ := raw_parts expressions rightInputs common secondContext rawSecond secondRaw
  obtain ⟨left,middle,firstCalls,firstKept,leftAvailable⟩ :=
    SourceCurrentStoredUnionObservations.members rawFirsts first common ready firstAvailable firstReplacements
  obtain ⟨right,reader,secondCalls,secondKept,rightAvailable⟩ :=
    SourceCurrentStoredUnionObservations.members rawSeconds second middle firstKept.ready
      (fun value member => firstKept.available value (secondAvailable value member))
      (fun name value found => firstKept.available value (secondReplacements name value found))
  have kept := firstKept.trans secondKept
  have valid := ready.semantic.1.normal.facts.coherent.valid
  have middleValid := firstKept.ready.semantic.1.normal.facts.coherent.valid
  have firstWarm := SourceCurrentStoredCallsReplay.replay firstCalls reader valid secondKept.growth
  have secondWarm := SourceCurrentStoredCallsReplay.replay secondCalls reader middleValid (grows_refl _)
  have firstSource := InternedFreshOrdinaryReplay.buildMany_replays expressions leftInputs common reader rawFirsts common valid firstMany kept.growth
  have secondSource := InternedFreshOrdinaryReplay.buildMany_replays expressions rightInputs common reader rawSeconds common valid secondMany kept.growth
  have firstReplacement : Replacements reader first := fun name value found => kept.available value (firstReplacements name value found)
  have secondReplacement : Replacements reader second := fun name value found => kept.available value (secondReplacements name value found)
  have memberCases : ∀ child ∈ expressions, ∀ executionReader, AlignedAt depth view executionReader child := by
    intro child member
    obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
    apply children index child found
    have strict := List.sizeOf_lt_of_mem member
    simp only [Syntax.union.sizeOf_spec]
    omega
  have matched := children_aligned expressions depth view reader
    (fun child member => memberCases child member reader)
    leftInputs rightInputs first second paired secondKept.ready
    (fun value member => kept.available value (firstInputs value member))
    (fun value member => kept.available value (secondInputs value member))
    firstReplacement secondReplacement rawFirsts rawSeconds left right firstSource secondSource firstWarm secondWarm
  have firstNormalized : run (makeUnion rawFirsts) reader = (rawFirst,reader) := by
    simpa only [firstMade] using InternedConstructorTemplates.replay (makeUnion rawFirsts) common reader valid
      (by simpa only [firstMade] using kept.growth)
  have secondNormalized : run (makeUnion rawSeconds) reader = (rawSecond,reader) := by
    simpa only [secondMade] using InternedConstructorTemplates.replay (makeUnion rawSeconds) common reader valid
      (by simpa only [secondMade] using kept.growth)
  have firstResult : execute rawFirst first reader = .done result reader :=
    InternedFreshOrdinaryReplay.build_replay (encode (leaves rawFirst) [] rawFirst)
      ((leaves rawFirst).map (input first)) common reader result common valid firstDone kept.growth
  have secondResult : execute rawSecond second reader = .done other reader :=
    InternedFreshOrdinaryReplay.build_replay (encode (leaves rawSecond) [] rawSecond)
      ((leaves rawSecond).map (input second)) common reader other common valid secondDone kept.growth
  have firstOriginals : Values reader rawFirsts := fun value member => kept.available value (firstAvailable value member)
  have secondOriginals : Values reader rawSeconds := fun value member => kept.available value (secondAvailable value member)
  have firstEmpty := SourceCurrentStoredUnionSurvival.warm_empty rawFirsts left first reader rawFirst result secondKept.ready
    firstOriginals firstReplacement firstWarm firstNormalized firstResult
  have secondEmpty := SourceCurrentStoredUnionSurvival.warm_empty rawSeconds right second reader rawSecond other secondKept.ready
    secondOriginals secondReplacement secondWarm secondNormalized secondResult
  have firstSame := SourceCurrentStoredUnionFusion.warm rawFirsts left first reader rawFirst result secondKept.ready
    firstOriginals firstReplacement firstWarm firstNormalized firstResult
  have secondSame := SourceCurrentStoredUnionFusion.warm rawSeconds right second reader rawSecond other secondKept.ready
    secondOriginals secondReplacement secondWarm secondNormalized secondResult
  exact ⟨firstEmpty.trans ((all_empty matched).trans secondEmpty.symm),
    (firstSame depth view).trans ((list_same matched).trans (secondSame depth view).symm)⟩


end MicroCFTA.SourceCurrentReaderFiniteUnionStep
