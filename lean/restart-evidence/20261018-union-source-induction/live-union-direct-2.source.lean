import MicroCFTA.SourceCurrentStoredLiveSourceLineage
import MicroCFTA.SourceCurrentStoredPairedUnionLineage
import MicroCFTA.SourceCurrentStoredUnionSurvival
import MicroCFTA.InternedStoredShallowCompletion

/-!
# Live-support source union reconstruction

Every union member inherits the exact live-support compatibility.
Actual member calls derive physical Empty agreement and all finite
observations through union normalization. Initial Ready inputs construct
both raw and stored calls without active source binders. Unused lexical
aliases remain permitted. Recursive captured values remain included.
-/
namespace MicroCFTA.SourceCurrentStoredLiveUnionLineage
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
open SourceCurrentStoredLiveSourceLineage (Aligned)
open SourceCurrentStoredProbeCompatibility (Compatible)
open InternedFreshOrdinaryLiveInputs (inputProfile)
open InternedBinderProtocol (Reference)
open SourceCurrentStoredPairedUnionLineage (StrictMember)
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

variable {Atom : Type}
private theorem member_compatible (expressions : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard)
    (compatible : Compatible (.union expressions) inputs firstNames secondNames first second)
    (child : Syntax Symbol Guard) (member : child ∈ expressions) :
    Compatible child inputs firstNames secondNames first second := by
  have included (label : Sum Reference Atom) (present : label ∈ SourceCurrentNativeNormalizationInputs.support child inputs) :
      label ∈ SourceCurrentNativeNormalizationInputs.support (.union expressions) inputs := by
    unfold SourceCurrentNativeNormalizationInputs.support at present ⊢
    rw [InternedFreeNameSemantics.evaluate]
    exact (InternedFreeNameSemantics.evaluateMany_member expressions (inputs.map inputProfile)
      (inputs.map SourceCurrentNativeNormalizationInputs.inputNames) label).mpr ⟨child,member,present⟩
  exact ⟨fun name present => compatible.1 name (included _ present),
    fun atom present => compatible.2 atom (included _ present)⟩

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
    (cases : ∀ expression ∈ expressions, Aligned expression)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard)
    (compatible : ∀ expression ∈ expressions, Compatible expression inputs firstNames secondNames first second)
    (common : State Symbol Guard) (ready : Ready common)
    (firstInputs : Values common (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)))
    (secondInputs : Values common (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)))
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second)
    (rawFirst rawSecond left right : List (Value Symbol Guard))
    (firstRaw : buildMany expressions (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)) common = .done rawFirst common)
    (secondRaw : buildMany expressions (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)) common = .done rawSecond common)
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
                  exact .cons (cases expression List.mem_cons_self Atom inputs firstNames secondNames first second (compatible expression List.mem_cons_self)
                    common ready firstInputs secondInputs firstReplacements secondReplacements _ _ firstRaw secondRaw
                    _ _ firstDone secondDone)
                    (ih (fun expression member => cases expression (List.mem_cons_of_mem _ member))
                      (fun expression member => compatible expression (List.mem_cons_of_mem _ member))
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
  intro Atom inputs firstNames secondNames first second compatible common ready firstInputs secondInputs
    firstReplacements secondReplacements rawFirst rawSecond firstRaw secondRaw result other firstDone secondDone
  let leftInputs := inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)
  let rightInputs := inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)
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
  have matched := children_aligned expressions memberCases inputs firstNames secondNames first second
    (fun child member => member_compatible expressions inputs firstNames secondNames first second compatible child member) reader secondKept.ready
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

/-- Live compatibility suffices for source syntax without active binders, including nested unions. -/
theorem binder_free (expression : Syntax Symbol Guard) (free : BinderFree expression) : Aligned expression := by
  cases shape : expression with
  | empty => exact SourceCurrentStoredLiveSourceLineage.empty
  | var index => exact SourceCurrentStoredLiveSourceLineage.reference index
  | binder smart body => simp only [shape,BinderFree] at free
  | node rows =>
      simp only [shape,BinderFree] at free
      apply SourceCurrentStoredLiveSourceLineage.ordinary rows
      intro child selected
      obtain ⟨symbol,guard,children,member,present,smaller⟩ := selected
      exact binder_free child (many_free children (edge_free rows free symbol guard children member) child present)
  | union expressions =>
      simp only [shape,BinderFree] at free
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

/-- Initial live-compatible inputs construct both raw and stored calls for source syntax without active binders. -/
theorem initial (expression : Syntax Symbol Guard) (free : BinderFree expression)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard)
    (compatible : Compatible expression inputs firstNames secondNames first second)
    (before : State Symbol Guard) (ready : Ready before)
    (firstInputs : Values before (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames))) (secondInputs : Values before (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)))
    (firstReplacements : Replacements before first) (secondReplacements : Replacements before second) :
    ∃ rawFirst after rawSecond common left middle right reader,
      build expression (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)) before = .done rawFirst after ∧
      build expression (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)) after = .done rawSecond common ∧
      execute rawFirst first common = .done left middle ∧ execute rawSecond second middle = .done right reader ∧
      execute rawFirst first reader = .done left reader ∧ execute rawSecond second reader = .done right reader ∧
      Keeps before after ∧ Keeps after common ∧ Keeps common middle ∧ Keeps middle reader ∧
      Available reader left ∧ Available reader right ∧
      Nonempty (SourceCurrentNativeMuPublication.History common middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle reader) ∧ Related left right := by
  obtain ⟨rawFirst,after,firstRaw⟩ := InternedRecordDepthCompletion.source_complete expression (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)) before
    (SourceRecursiveIntersectionSemanticHeap.context before ready.semantic (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)) firstInputs)
    ready.semantic.2 ready.covered
  have firstKept := source_keeps expression (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)) before after ready firstInputs rawFirst firstRaw
  have rightAvailable : Values after (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)) := fun value member => firstKept.available value (secondInputs value member)
  obtain ⟨rawSecond,common,secondRaw⟩ := InternedRecordDepthCompletion.source_complete expression (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)) after
    (SourceRecursiveIntersectionSemanticHeap.context after firstKept.ready.semantic (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)) rightAvailable)
    firstKept.ready.semantic.2 firstKept.ready.covered
  have secondKept := source_keeps expression (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)) after common firstKept.ready rightAvailable rawSecond secondRaw
  have kept := firstKept.trans secondKept
  obtain ⟨left,middle,right,reader,firstDone,secondDone,firstWarm,secondWarm,firstStored,secondStored,
    leftAvailable,rightOutput,firstHistory,secondHistory,related⟩ := SourceCurrentStoredLiveSourceLineage.complete expression (binder_free expression free)
      inputs firstNames secondNames first second compatible before after after common common
      (SourceRecursiveIntersectionSemanticHeap.context before ready.semantic (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)) firstInputs)
      (SourceRecursiveIntersectionSemanticHeap.context after firstKept.ready.semantic (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)) rightAvailable)
      rawFirst rawSecond firstRaw secondRaw secondKept.growth (grows_refl _) secondKept.ready
      (fun value member => kept.available value (firstInputs value member))
      (fun value member => kept.available value (secondInputs value member))
      (fun name value found => kept.available value (firstReplacements name value found))
      (fun name value found => kept.available value (secondReplacements name value found))
  exact ⟨rawFirst,after,rawSecond,common,left,middle,right,reader,firstRaw,secondRaw,firstDone,secondDone,
    firstWarm,secondWarm,firstKept,secondKept,firstStored,secondStored,leftAvailable,rightOutput,
    firstHistory,secondHistory,related⟩


end MicroCFTA.SourceCurrentStoredLiveUnionLineage
