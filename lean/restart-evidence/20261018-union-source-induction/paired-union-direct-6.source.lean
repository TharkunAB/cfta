import MicroCFTA.SourceCurrentStoredPairedOrdinaryLineage
import MicroCFTA.SourceCurrentStoredUnionSurvival
import MicroCFTA.InternedStoredShallowCompletion

/-!
# Paired source union reconstruction

Strict source-member induction compares actual union member returns.
Actual normalization then derives physical Empty agreement and every
finite observation. Initial Ready data constructs both stored calls.
Source syntax without active binders can still capture recursive values.
-/
namespace MicroCFTA.SourceCurrentStoredPairedUnionLineage
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentOpenObservationSurvival (Related)
open SourceCurrentOpenObservations (Same)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentStoredMuBinderChildLineage (Paired)
open SourceCurrentStoredPairedOrdinaryLineage (Aligned)
open InternedStoredShallowCompletion (BinderFree ManyBinderFree EdgesBinderFree)
open Language
private theorem many_free (expressions : List (Syntax Symbol Guard)) (free : ManyBinderFree expressions)
    (child : Syntax Symbol Guard) (member : child ∈ expressions) : BinderFree child := by
  induction expressions with
  | nil => cases member
  | cons expression rest ih =>
      simp only [ManyBinderFree] at free
      rcases List.mem_cons.mp member with rfl | later
      · exact free.1
      · exact ih free.2 later

private theorem edge_free (expressions : List (EdgeSyntax Symbol Guard)) (free : EdgesBinderFree expressions)
    (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (member : EdgeSyntax.mk symbol guard children ∈ expressions) : ManyBinderFree children := by
  induction expressions with
  | nil => cases member
  | cons expression rest ih =>
      cases expression with
      | mk ownSymbol ownGuard originals =>
          simp only [EdgesBinderFree] at free
          rcases List.mem_cons.mp member with same | later
          · cases same
            exact free.1
          · exact ih free.2 later

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A union induction index retains its original member and strict source-size decrease. -/
def StrictMember (expressions : List (Syntax Symbol Guard)) (child : Syntax Symbol Guard) : Prop :=
  child ∈ expressions ∧ sizeOf child < sizeOf (.union expressions : Syntax Symbol Guard)

/-- Empty source syntax has the same exact reconstructed empty result under paired inputs. -/
theorem empty : Aligned (Symbol := Symbol) (Guard := Guard) .empty := by
  intro left right first second paired common ready leftAvailable rightAvailable firstReplacements secondReplacements
    rawFirst rawSecond firstRaw secondRaw result other firstDone secondDone
  simp only [build,Outcome.done.injEq] at firstRaw secondRaw
  obtain ⟨rfl,_⟩ := firstRaw
  obtain ⟨rfl,_⟩ := secondRaw
  have firstEqual := (Outcome.done.inj ((SourceCurrentStoredUnionObservations.closed .empty first common rfl).symm.trans firstDone)).1
  have secondEqual := (Outcome.done.inj ((SourceCurrentStoredUnionObservations.closed .empty second common rfl).symm.trans secondDone)).1
  rw [← firstEqual,← secondEqual]
  exact ⟨Iff.rfl,fun depth view => Same.refl depth view [.empty]⟩

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
    (cases : ∀ expression ∈ expressions, Aligned expression)
    (leftInputs rightInputs : List (Value Symbol Guard))
    (first second : Environment Symbol Guard) (paired : Paired first second leftInputs rightInputs)
    (common : State Symbol Guard) (ready : Ready common)
    (firstInputs : Values common leftInputs)
    (secondInputs : Values common rightInputs)
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second)
    (rawFirst rawSecond left right : List (Value Symbol Guard))
    (firstRaw : buildMany expressions leftInputs common = .done rawFirst common)
    (secondRaw : buildMany expressions rightInputs common = .done rawSecond common)
    (firstDone : All₂ (fun raw output => execute raw first common = .done output common) rawFirst left)
    (secondDone : All₂ (fun raw output => execute raw second common = .done output common) rawSecond right) :
    All₂ Related left right := by
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
                    common ready firstInputs secondInputs firstReplacements secondReplacements _ _ firstRaw secondRaw
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

private theorem all_empty {first second : List (Value Symbol Guard)} (paired : All₂ Related first second) :
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

private theorem list_same {first second : List (Value Symbol Guard)} (paired : All₂ Related first second)
    (depth : Nat) (view : State Symbol Guard) : Same depth view first second := by
  induction paired with
  | nil => exact Same.refl depth view []
  | @cons first second rest remaining head tail ih =>
      simpa only [List.singleton_append] using
        SourceCurrentOpenObservationLists.append depth view [first] [second] rest remaining (head.2 depth view) ih

/-- Strict member induction derives union reconstruction agreement through actual source normalization. -/
theorem union (expressions : List (Syntax Symbol Guard))
    (children : ∀ child, StrictMember expressions child → Aligned child) : Aligned (.union expressions) := by
  intro leftInputs rightInputs first second paired common ready firstInputs secondInputs
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
  have memberCases : ∀ child ∈ expressions, Aligned child := by
    intro child member
    apply children child ⟨member,?_⟩
    have strict := List.sizeOf_lt_of_mem member
    simp only [Syntax.union.sizeOf_spec]
    omega
  have matched := children_aligned expressions memberCases leftInputs rightInputs first second paired reader secondKept.ready
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
    fun depth view => (firstSame depth view).trans ((list_same matched depth view).trans (secondSame depth view).symm)⟩

/-- Initial Ready data constructs both stored calls from actual earlier raw calls and an established source case. -/
theorem complete (expression : Syntax Symbol Guard) (aligned : Aligned expression)
    (leftInputs rightInputs : List (Value Symbol Guard))
    (first second : Environment Symbol Guard) (paired : Paired first second leftInputs rightInputs)
    (before after later final common : State Symbol Guard)
    (firstContext : Context before leftInputs)
    (secondContext : Context later rightInputs)
    (rawFirst rawSecond : Value Symbol Guard)
    (firstRaw : build expression leftInputs before = .done rawFirst after)
    (secondRaw : build expression rightInputs later = .done rawSecond final)
    (firstGrowth : Grows after common) (secondGrowth : Grows final common)
    (ready : Ready common)
    (firstInputs : Values common leftInputs)
    (secondInputs : Values common rightInputs)
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second) :
    ∃ left middle right reader,
      execute rawFirst first common = .done left middle ∧ execute rawSecond second middle = .done right reader ∧
      execute rawFirst first reader = .done left reader ∧ execute rawSecond second reader = .done right reader ∧
      Keeps common middle ∧ Keeps middle reader ∧ Available reader left ∧ Available reader right ∧
      Nonempty (SourceCurrentNativeMuPublication.History common middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle reader) ∧ Related left right := by
  have firstWarm := InternedFreshOrdinaryReplay.build_replay expression _ before common rawFirst after
    firstContext.normal.facts.coherent.valid firstRaw firstGrowth
  have secondWarm := InternedFreshOrdinaryReplay.build_replay expression _ later common rawSecond final
    secondContext.normal.facts.coherent.valid secondRaw secondGrowth
  have firstAvailable := (InternedFreshOrdinaryFacts.build_verified expression _ common
    ready.semantic.1.normal.facts firstInputs).result rawFirst common firstWarm
  have secondAvailable := (InternedFreshOrdinaryFacts.build_verified expression _ common
    ready.semantic.1.normal.facts secondInputs).result rawSecond common secondWarm
  obtain ⟨left,middle,firstDone,firstKept,leftAvailable,firstHistory⟩ :=
    SourceCurrentStoredReconstruction.execute rawFirst first common ready firstAvailable firstReplacements
  obtain ⟨right,reader,secondDone,secondKept,rightAvailable,secondHistory⟩ :=
    SourceCurrentStoredReconstruction.execute rawSecond second middle firstKept.ready
      (firstKept.available rawSecond secondAvailable)
      (fun name value found => firstKept.available value (secondReplacements name value found))
  have firstReplay := InternedFreshOrdinaryReplay.build_replay (encode (leaves rawFirst) [] rawFirst)
    ((leaves rawFirst).map (input first)) common reader left middle ready.semantic.1.normal.facts.coherent.valid
    firstDone secondKept.growth
  have secondReplay := InternedFreshOrdinaryReplay.build_replay (encode (leaves rawSecond) [] rawSecond)
    ((leaves rawSecond).map (input second)) middle reader right reader firstKept.ready.semantic.1.normal.facts.coherent.valid
    secondDone (grows_refl _)
  have growth := grows_trans firstKept.growth secondKept.growth
  have firstSource := InternedFreshOrdinaryReplay.build_replay expression _ before reader rawFirst after
    firstContext.normal.facts.coherent.valid firstRaw (grows_trans firstGrowth growth)
  have secondSource := InternedFreshOrdinaryReplay.build_replay expression _ later reader rawSecond final
    secondContext.normal.facts.coherent.valid secondRaw (grows_trans secondGrowth growth)
  have compared := aligned leftInputs rightInputs first second paired reader secondKept.ready
    (fun value member => secondKept.available value (firstKept.available value (firstInputs value member)))
    (fun value member => secondKept.available value (firstKept.available value (secondInputs value member)))
    (fun name value found => secondKept.available value (firstKept.available value (firstReplacements name value found)))
    (fun name value found => secondKept.available value (firstKept.available value (secondReplacements name value found)))
    rawFirst rawSecond firstSource secondSource left right firstReplay secondReplay
  exact ⟨left,middle,right,reader,firstDone,secondDone,firstReplay,secondReplay,firstKept,secondKept,
    secondKept.available left leftAvailable,rightAvailable,firstHistory,secondHistory,compared⟩

/-- All source syntax without active binders satisfies paired reconstruction agreement, including nested unions. -/
theorem binder_free (expression : Syntax Symbol Guard) (free : BinderFree expression) : Aligned expression := by
  cases shape : expression with
  | empty => exact empty
  | var index => exact SourceCurrentStoredPairedOrdinaryLineage.reference index
  | binder smart body => simp only [BinderFree] at free
  | node rows =>
      simp only [BinderFree] at free
      apply SourceCurrentStoredPairedOrdinaryLineage.ordinary rows
      intro child selected
      obtain ⟨symbol,guard,children,member,present,smaller⟩ := selected
      exact binder_free child (many_free children (edge_free rows free symbol guard children member) child present)
  | union expressions =>
      simp only [BinderFree] at free
      apply union expressions
      intro child selected
      have smaller := selected.2
      exact binder_free child (many_free expressions free child selected.1)
termination_by sizeOf expression
decreasing_by all_goals simpa only [shape] using smaller

private theorem source_keeps (expression : Syntax Symbol Guard) (inputs : List (Value Symbol Guard))
    (before after : State Symbol Guard) (ready : Ready before) (available : Values before inputs)
    (value : Value Symbol Guard) (actual : build expression inputs before = .done value after) : Keeps before after := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic inputs available
  have checked := InternedFreshOrdinaryFacts.build_verified expression inputs before ready.semantic.1.normal.facts available
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source expression inputs before ready.semantic available
  · exact InternedFreshOrdinaryCoverage.build_covered expression inputs before
      ready.semantic.1.normal.facts.coherent.valid ready.covered value after actual
  · simpa only [actual,Outcome.state] using
      (InternedOpenDepthExecution.build_depth expression inputs before context ready.semantic.2 ready.depth).heap
  · simpa only [actual,Outcome.state] using checked.growth
  · simpa only [actual,Outcome.state] using checked.history

/-- Initial paired inputs construct both raw and stored executions for source syntax without active binders. -/
theorem initial (expression : Syntax Symbol Guard) (free : BinderFree expression)
    (leftInputs rightInputs : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (paired : Paired first second leftInputs rightInputs)
    (before : State Symbol Guard) (ready : Ready before)
    (firstInputs : Values before leftInputs) (secondInputs : Values before rightInputs)
    (firstReplacements : Replacements before first) (secondReplacements : Replacements before second) :
    ∃ rawFirst after rawSecond common left middle right reader,
      build expression leftInputs before = .done rawFirst after ∧
      build expression rightInputs after = .done rawSecond common ∧
      execute rawFirst first common = .done left middle ∧ execute rawSecond second middle = .done right reader ∧
      execute rawFirst first reader = .done left reader ∧ execute rawSecond second reader = .done right reader ∧
      Keeps before after ∧ Keeps after common ∧ Keeps common middle ∧ Keeps middle reader ∧
      Available reader left ∧ Available reader right ∧
      Nonempty (SourceCurrentNativeMuPublication.History common middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle reader) ∧ Related left right := by
  obtain ⟨rawFirst,after,firstRaw⟩ := InternedRecordDepthCompletion.source_complete expression leftInputs before
    (SourceRecursiveIntersectionSemanticHeap.context before ready.semantic leftInputs firstInputs)
    ready.semantic.2 ready.covered
  have firstKept := source_keeps expression leftInputs before after ready firstInputs rawFirst firstRaw
  have rightAvailable : Values after rightInputs := fun value member => firstKept.available value (secondInputs value member)
  obtain ⟨rawSecond,common,secondRaw⟩ := InternedRecordDepthCompletion.source_complete expression rightInputs after
    (SourceRecursiveIntersectionSemanticHeap.context after firstKept.ready.semantic rightInputs rightAvailable)
    firstKept.ready.semantic.2 firstKept.ready.covered
  have secondKept := source_keeps expression rightInputs after common firstKept.ready rightAvailable rawSecond secondRaw
  have kept := firstKept.trans secondKept
  obtain ⟨left,middle,right,reader,firstDone,secondDone,firstWarm,secondWarm,firstStored,secondStored,
    leftAvailable,rightOutput,firstHistory,secondHistory,related⟩ := complete expression (binder_free expression free)
      leftInputs rightInputs first second paired before after after common common
      (SourceRecursiveIntersectionSemanticHeap.context before ready.semantic leftInputs firstInputs)
      (SourceRecursiveIntersectionSemanticHeap.context after firstKept.ready.semantic rightInputs rightAvailable)
      rawFirst rawSecond firstRaw secondRaw secondKept.growth (grows_refl _) secondKept.ready
      (fun value member => kept.available value (firstInputs value member))
      (fun value member => kept.available value (secondInputs value member))
      (fun name value found => kept.available value (firstReplacements name value found))
      (fun name value found => kept.available value (secondReplacements name value found))
  exact ⟨rawFirst,after,rawSecond,common,left,middle,right,reader,firstRaw,secondRaw,firstDone,secondDone,
    firstWarm,secondWarm,firstKept,secondKept,firstStored,secondStored,leftAvailable,rightOutput,
    firstHistory,secondHistory,related⟩


end MicroCFTA.SourceCurrentStoredPairedUnionLineage
