import MicroCFTA.SourceCurrentPublicationFilterSource
import MicroCFTA.SourceCurrentStoredLiteralCongruence
import MicroCFTA.SourceCurrentPublicationBareParity

/-!
# Filtered publication reconstruction without source binders

The source proof removes the local only along the root union spine.
Exact root parts transport that transformation through stored calls.
Actual publication freshness retains arbitrary recursive captured records.
-/
namespace MicroCFTA.SourceCurrentPublicationFilterAlignment
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryLiveInputs (input liftInput local_inputs)
open InternedStoredSubstitution (Environment Replacements leaves encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentStoredProbeCompatibility (Compatible)
open SourceCurrentLiteralRootParts (SameParts)
open SourceCurrentNativeCallbackErasure (eraseSelf)
open SourceCurrentPublicationFilterSource (rootErase)
open SourceCurrentOpenObservationSurvival (Related)
open InternedBinderProtocol (Reference)

private theorem output_available [DecidableEq (EdgeKey Symbol Guard)]
    (value output : Value Symbol Guard) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) (ready : Ready state) (available : Available state value)
    (replacements : Replacements state environment)
    (actual : execute value environment state = .done output state) : Available state output :=
  (InternedFreshOrdinaryFacts.build_verified (encode (leaves value) [] value)
    ((leaves value).map (InternedStoredSubstitution.input environment)) state ready.semantic.1.normal.facts
    (InternedStoredSubstitution.inputs_available value environment state available replacements)).result output state actual

private theorem parts_chain [DecidableEq (EdgeKey Symbol Guard)]
    (first second third fourth : Value Symbol Guard)
    (left : Related first second) (middle : Related second third) (right : Related fourth third) :
    Related first fourth :=
  ⟨left.1.trans (middle.1.trans right.1.symm),fun depth view =>
    (left.2 depth view).trans ((middle.2 depth view).trans (right.2 depth view).symm)⟩

private theorem warm_nonbare [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (free : InternedStoredShallowCompletion.BinderFree event.expression)
    (common : State Symbol Guard) (current : Keeps event.afterBody common)
    (replacement : Value Symbol Guard) (available : Available common replacement)
    (left right : Value Symbol Guard)
    (bodyNotBare : event.body ≠ .reference (.interned event.entry.identity))
    (ordinaryNotBare : event.ordinary ≠ .reference (.uninterned (ordinaryLevel event.depth)))
    (firstDone : execute event.body
      (fun name => if name = .interned event.entry.identity then some replacement else none) common = .done left common)
    (secondDone : execute event.ordinary
      (fun name => if name = .uninterned (ordinaryLevel event.depth) then some replacement else none) common = .done right common) :
    Related left right := by
  let inputs : List (Sum (Value Symbol Guard) Unit) := event.environment.map Sum.inl
  let names : Unit → Reference := fun _ => .depth
  let bodyInputs := .inr (.inl ()) :: inputs.map liftInput
  let ordinaryName : Reference := .uninterned (ordinaryLevel event.depth)
  let bodyName : Reference := .interned event.entry.identity
  let ordinaryNames := Sum.elim (fun _ : Unit => ordinaryName) names
  let bodyNames := Sum.elim (fun _ : Unit => bodyName) names
  let ordinaryMap : Environment Symbol Guard := fun name => if name = ordinaryName then some replacement else none
  let bodyMap : Environment Symbol Guard := fun name => if name = bodyName then some replacement else none
  have fixed : inputs.map (input names) = event.environment := by
    simp [inputs,input,List.map_map,Function.comp_def]
  have localMap (own : Reference) :
      bodyInputs.map (input (Sum.elim (fun _ : Unit => own) names)) = .reference own :: event.environment := by
    rw [local_inputs,fixed]
  obtain ⟨rawOrdinary,afterRawOrdinary,rawBody,afterRawBody,ordinaryDone,ordinaryFilter,bodyDone,bodyFilter,
    ordinaryGrowth,bodyGrowth,ordinaryEntry,bodyEntry⟩ := SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  have ordinaryArgument : Available event.afterDepth (.reference ordinaryName) :=
    InternedNestedProvenance.ordinary_available _ _
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have bodyArgument : Available event.allocated (.reference bodyName) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have ordinaryContext := ordinaryEntry.base.local ordinaryName ordinaryArgument
  have bodyContext := bodyEntry.base.local bodyName bodyArgument
  have ordinaryFresh : ordinaryName ∉
      (SourceCurrentNativeNormalizationInputs.support (.binder true event.expression) inputs).map (Sum.elim id names) :=
    SourceCurrentNativeNormalizationFreshness.ordinary event.expression inputs names event.before event.afterDepth
      (by simpa only [fixed] using event.context.base) event.depth (by simpa only [fixed] using event.depthDone)
  have bodyFresh : bodyName ∉
      (SourceCurrentNativeNormalizationInputs.support (.binder true event.expression) inputs).map (Sum.elim id names) :=
    SourceCurrentNativeNormalizationFreshness.reserved (.binder true event.expression) inputs names event.cut
      (by simpa only [fixed] using cutContext.base) event.key event.missing
  have baseCompatible : Compatible (.binder true event.expression) inputs names names
      (fun _ => none) (fun _ => none) := ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  have compatible : Compatible event.expression bodyInputs bodyNames ordinaryNames bodyMap ordinaryMap := by
    apply SourceCurrentStoredProbeCompatibility.extend event.expression inputs names names
      (fun _ => none) (fun _ => none) baseCompatible bodyName ordinaryName replacement
    intro label member
    constructor
    · intro same
      exact False.elim (bodyFresh (List.mem_map.mpr ⟨label,member,same⟩))
    · intro same
      exact False.elim (ordinaryFresh (List.mem_map.mpr ⟨label,member,same⟩))
  have bodyCallback : callback event.expression event.environment bodyName event.allocated =
      .done event.body event.afterBody := event.bodyDone
  have checked := callback_verified event.expression event.environment bodyName event.allocated
    bodyEntry.base.normal.facts bodyContext.inputs
  have captures : Values event.afterBody event.environment := by
    intro value member
    simpa only [bodyCallback,Outcome.state] using checked.available value (bodyEntry.base.inputs value member)
  have bodyAtEnd : Available event.afterBody (.reference bodyName) := by
    simpa only [bodyCallback,Outcome.state] using checked.available (.reference bodyName) bodyArgument
  have ordinaryInputs : Values common (bodyInputs.map (input ordinaryNames)) := by
    rw [localMap]
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact InternedNestedProvenance.ordinary_available _ _
    · exact current.available value (captures value member)
  have bodyInputsAvailable : Values common (bodyInputs.map (input bodyNames)) := by
    rw [localMap]
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact current.available _ bodyAtEnd
    · exact current.available value (captures value member)
  have bodyReplacements : Replacements common bodyMap := by
    intro name value found
    dsimp only [bodyMap] at found
    split at found
    · cases found; exact available
    · cases found
  have ordinaryReplacements : Replacements common ordinaryMap := by
    intro name value found
    dsimp only [ordinaryMap] at found
    split at found
    · cases found; exact available
    · cases found
  have eraseCompatible : Compatible (rootErase event.expression) bodyInputs bodyNames ordinaryNames bodyMap ordinaryMap :=
    ⟨fun name member => compatible.1 name
      (SourceCurrentPublicationFilterSource.support_included event.expression bodyInputs (.inl name) member),
     fun atom member => compatible.2 atom
      (SourceCurrentPublicationFilterSource.support_included event.expression bodyInputs (.inr atom) member)⟩
  obtain ⟨erasedBody,afterErasedBody,erasedOrdinary,erasedCommon,erasedLeft,erasedMiddle,erasedRight,reader,
    erasedBodyDone,erasedOrdinaryDone,erasedFirst,erasedSecond,erasedFirstWarm,erasedSecondWarm,
    firstSourceKept,secondSourceKept,firstStoredKept,secondStoredKept,erasedLeftAvailable,erasedRightAvailable,
    _,_,erasedRelated⟩ := SourceCurrentStoredLiveUnionLineage.initial (rootErase event.expression)
      (SourceCurrentPublicationFilterSource.rootErase_binder_free event.expression free)
      bodyInputs bodyNames ordinaryNames bodyMap ordinaryMap eraseCompatible common current.ready
      bodyInputsAvailable ordinaryInputs bodyReplacements ordinaryReplacements
  have sourceKept := firstSourceKept.trans secondSourceKept
  have storedKept := firstStoredKept.trans secondStoredKept
  have kept := sourceKept.trans storedKept
  have readerReady := secondStoredKept.ready
  have bodyInputsReader : Values reader (bodyInputs.map (input bodyNames)) :=
    fun value member => kept.available value (bodyInputsAvailable value member)
  have ordinaryInputsReader : Values reader (bodyInputs.map (input ordinaryNames)) :=
    fun value member => kept.available value (ordinaryInputs value member)
  have bodyReplacementsReader : Replacements reader bodyMap :=
    fun name value found => kept.available value (bodyReplacements name value found)
  have ordinaryReplacementsReader : Replacements reader ordinaryMap :=
    fun name value found => kept.available value (ordinaryReplacements name value found)
  have bodyRawWarm := InternedFreshOrdinaryReplay.build_replay event.expression _ event.allocated reader rawBody afterRawBody
    bodyContext.normal.facts.coherent.valid bodyDone (grows_trans bodyGrowth (grows_trans current.growth kept.growth))
  have ordinaryRawWarm := InternedFreshOrdinaryReplay.build_replay event.expression _ event.afterDepth reader rawOrdinary afterRawOrdinary
    ordinaryContext.normal.facts.coherent.valid ordinaryDone (grows_trans ordinaryGrowth (grows_trans current.growth kept.growth))
  have bodyErasedWarm := InternedFreshOrdinaryReplay.build_replay (rootErase event.expression) _ common reader erasedBody afterErasedBody
    current.ready.semantic.1.normal.facts.coherent.valid erasedBodyDone (grows_trans secondSourceKept.growth storedKept.growth)
  have ordinaryErasedWarm := InternedFreshOrdinaryReplay.build_replay (rootErase event.expression) _ afterErasedBody reader erasedOrdinary erasedCommon
    firstSourceKept.ready.semantic.1.normal.facts.coherent.valid erasedOrdinaryDone storedKept.growth
  have bodyContextReader : InternedFreshOrdinaryContext.Context reader (.reference bodyName :: event.environment) :=
    ⟨readerReady.semantic.1.normal,by simpa only [bodyNames,localMap] using bodyInputsReader,
      readerReady.semantic.1.profiles,readerReady.semantic.1.freeNames⟩
  have ordinaryContextReader : InternedFreshOrdinaryContext.Context reader (.reference ordinaryName :: event.environment) :=
    ⟨readerReady.semantic.1.normal,by simpa only [ordinaryNames,localMap] using ordinaryInputsReader,
      readerReady.semantic.1.profiles,readerReady.semantic.1.freeNames⟩
  have bodyFreshEval : bodyName ∉ InternedFreeNameSemantics.evaluate (.binder true event.expression)
      (event.environment.map InternedRootProfile.profile) (event.environment.map Value.free) := by
    rw [SourceCurrentNativeNormalizationInputs.instantiated,fixed] at bodyFresh
    exact bodyFresh
  have ordinaryFreshEval : ordinaryName ∉ InternedFreeNameSemantics.evaluate (.binder true event.expression)
      (event.environment.map InternedRootProfile.profile) (event.environment.map Value.free) := by
    rw [SourceCurrentNativeNormalizationInputs.instantiated,fixed] at ordinaryFresh
    exact ordinaryFresh
  have bodySourceParts := SourceCurrentPublicationFilterSource.source_parts event.expression free event.environment bodyName
    bodyFreshEval reader bodyContextReader rawBody erasedBody bodyRawWarm (by simpa only [bodyNames,localMap] using bodyErasedWarm)
  have ordinarySourceParts := SourceCurrentPublicationFilterSource.source_parts event.expression free event.environment ordinaryName
    ordinaryFreshEval reader ordinaryContextReader rawOrdinary erasedOrdinary ordinaryRawWarm
    (by simpa only [ordinaryNames,localMap] using ordinaryErasedWarm)
  have bodyRawContext : InternedFreshOrdinaryContext.Context afterRawBody (.reference bodyName :: event.environment) := by
    simpa only [bodyName,bodyDone,Outcome.state] using bodyContext.build event.expression
  have ordinaryRawContext : InternedFreshOrdinaryContext.Context afterRawOrdinary (.reference ordinaryName :: event.environment) := by
    simpa only [ordinaryName,ordinaryDone,Outcome.state] using ordinaryContext.build event.expression
  have bodyRawAvailable := (InternedFreshOrdinaryFacts.build_verified event.expression _ event.allocated
    bodyContext.normal.facts bodyContext.inputs).result rawBody afterRawBody bodyDone
  have ordinaryRawAvailable := (InternedFreshOrdinaryFacts.build_verified event.expression _ event.afterDepth
    ordinaryContext.normal.facts ordinaryContext.inputs).result rawOrdinary afterRawOrdinary ordinaryDone
  have bodyRawReader := (InternedFreshOrdinaryFacts.build_verified event.expression _ reader
    bodyContextReader.normal.facts bodyContextReader.inputs).result rawBody reader bodyRawWarm
  have ordinaryRawReader := (InternedFreshOrdinaryFacts.build_verified event.expression _ reader
    ordinaryContextReader.normal.facts ordinaryContextReader.inputs).result rawOrdinary reader ordinaryRawWarm
  have bodyParts : SameParts (eraseSelf bodyName event.body) erasedBody := by
    constructor
    · intro atom
      have past := SourceCurrentPublicationFilterSource.filtered_literal afterRawBody bodyRawContext.normal bodyName rawBody bodyRawAvailable atom
      rw [bodyFilter] at past
      exact past.trans ((SourceCurrentPublicationFilterSource.filtered_literal reader readerReady.semantic.1.normal
        bodyName rawBody bodyRawReader atom).symm.trans (bodySourceParts.1 atom))
    · intro row
      have past := SourceCurrentPublicationFilterSource.filtered_row afterRawBody bodyRawContext.normal bodyName rawBody bodyRawAvailable row
      rw [bodyFilter] at past
      exact past.trans ((SourceCurrentPublicationFilterSource.filtered_row reader readerReady.semantic.1.normal
        bodyName rawBody bodyRawReader row).symm.trans (bodySourceParts.2 row))
  have ordinaryParts : SameParts (eraseSelf ordinaryName event.ordinary) erasedOrdinary := by
    constructor
    · intro atom
      have past := SourceCurrentPublicationFilterSource.filtered_literal afterRawOrdinary ordinaryRawContext.normal ordinaryName rawOrdinary ordinaryRawAvailable atom
      rw [ordinaryFilter] at past
      exact past.trans ((SourceCurrentPublicationFilterSource.filtered_literal reader readerReady.semantic.1.normal
        ordinaryName rawOrdinary ordinaryRawReader atom).symm.trans (ordinarySourceParts.1 atom))
    · intro row
      have past := SourceCurrentPublicationFilterSource.filtered_row afterRawOrdinary ordinaryRawContext.normal ordinaryName rawOrdinary ordinaryRawAvailable row
      rw [ordinaryFilter] at past
      exact past.trans ((SourceCurrentPublicationFilterSource.filtered_row reader readerReady.semantic.1.normal
        ordinaryName rawOrdinary ordinaryRawReader row).symm.trans (ordinarySourceParts.2 row))
  have bodyEraseSame : eraseSelf bodyName event.body = event.body := by
    simp only [eraseSelf,show event.body.referenceOf ≠ .ref bodyName from
      fun same => bodyNotBare ((referenceOf_self_iff bodyName event.body).mp same),↓reduceIte]
  have ordinaryEraseSame : eraseSelf ordinaryName event.ordinary = event.ordinary := by
    simp only [eraseSelf,show event.ordinary.referenceOf ≠ .ref ordinaryName from
      fun same => ordinaryNotBare ((referenceOf_self_iff ordinaryName event.ordinary).mp same),↓reduceIte]
  rw [bodyEraseSame] at bodyParts
  rw [ordinaryEraseSame] at ordinaryParts
  have bodyAvailableEnd := checked.result event.body event.afterBody bodyCallback
  have ordinaryAvailableCut := (callback_verified event.expression event.environment ordinaryName event.afterDepth
    ordinaryEntry.base.normal.facts ordinaryContext.inputs).result event.ordinary event.cut event.ordinaryDone
  have bodyAvailableReader := kept.available event.body (current.available event.body bodyAvailableEnd)
  have bodyErasedAvailable := (InternedFreshOrdinaryFacts.build_verified (rootErase event.expression) _ reader
    readerReady.semantic.1.normal.facts bodyInputsReader).result erasedBody reader bodyErasedWarm
  have ordinaryErasedAvailable := (InternedFreshOrdinaryFacts.build_verified (rootErase event.expression) _ reader
    readerReady.semantic.1.normal.facts ordinaryInputsReader).result erasedOrdinary reader ordinaryErasedWarm
  have ordinaryAvailableAllocated : Available event.allocated event.ordinary :=
    ordinaryAvailableCut.grows event.cut event.allocated
      ⟨extends_refl _,InternedBinderProtocol.intern_grows _ _,extends_refl _,extends_refl _⟩
      (InternedFreshProbeKeys.intern_issued_extends event.cut.nodes event.key cutContext.base.normal.facts.coherent.valid.2)
  have ordinaryAvailableEnd : Available event.afterBody event.ordinary := by
    simpa only [bodyCallback,Outcome.state] using checked.available event.ordinary ordinaryAvailableAllocated
  have ordinaryAvailableReader := kept.available event.ordinary (current.available event.ordinary ordinaryAvailableEnd)
  have firstWarm : execute event.body bodyMap reader = .done left reader :=
    InternedFreshOrdinaryReplay.build_replay (encode (leaves event.body) [] event.body)
      ((leaves event.body).map (InternedStoredSubstitution.input bodyMap)) common reader left common
      current.ready.semantic.1.normal.facts.coherent.valid firstDone kept.growth
  have secondWarm : execute event.ordinary ordinaryMap reader = .done right reader :=
    InternedFreshOrdinaryReplay.build_replay (encode (leaves event.ordinary) [] event.ordinary)
      ((leaves event.ordinary).map (InternedStoredSubstitution.input ordinaryMap)) common reader right common
      current.ready.semantic.1.normal.facts.coherent.valid secondDone kept.growth
  have firstParts := SourceCurrentStoredLiteralCongruence.warm event.body erasedBody left erasedLeft bodyMap reader readerReady
    bodyAvailableReader bodyErasedAvailable bodyReplacementsReader bodyParts firstWarm erasedFirstWarm
  have secondParts := SourceCurrentStoredLiteralCongruence.warm event.ordinary erasedOrdinary right erasedRight ordinaryMap reader readerReady
    ordinaryAvailableReader ordinaryErasedAvailable ordinaryReplacementsReader ordinaryParts secondWarm erasedSecondWarm
  have leftAvailable := output_available event.body left bodyMap reader readerReady bodyAvailableReader bodyReplacementsReader firstWarm
  have rightAvailable := output_available event.ordinary right ordinaryMap reader readerReady ordinaryAvailableReader ordinaryReplacementsReader secondWarm
  exact parts_chain left erasedLeft erasedRight right
    (SourceCurrentLiteralPartsObservations.related reader reader readerReady.semantic.1.normal readerReady.semantic.1.normal
      left erasedLeft leftAvailable erasedLeftAvailable firstParts)
    erasedRelated
    (SourceCurrentLiteralPartsObservations.related reader reader readerReady.semantic.1.normal readerReady.semantic.1.normal
      right erasedRight rightAvailable erasedRightAvailable secondParts)

private theorem reference_execute [DecidableEq (EdgeKey Symbol Guard)]
    (name : Reference) (environment : Environment Symbol Guard) (state : State Symbol Guard) :
    execute (.reference name) environment state = .done ((environment name).getD (.reference name)) state := by
  simp [execute,leaves,Value.free,encode,InternedStoredSubstitution.slot,build,InternedStoredSubstitution.input]

/-- Actual warm reconstructions of both filtered callbacks agree for every BinderFree publication body. -/
theorem warm [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (free : InternedStoredShallowCompletion.BinderFree event.expression)
    (common : State Symbol Guard) (current : Keeps event.afterBody common)
    (replacement : Value Symbol Guard) (available : Available common replacement)
    (left right : Value Symbol Guard)
    (firstDone : execute event.body
      (fun name => if name = .interned event.entry.identity then some replacement else none) common = .done left common)
    (secondDone : execute event.ordinary
      (fun name => if name = .uninterned (ordinaryLevel event.depth) then some replacement else none) common = .done right common) :
    Related left right := by
  by_cases bare : event.body = .reference (.interned event.entry.identity)
  · have ordinaryBare := (SourceCurrentPublicationBareParity.bare event).mp bare
    rw [bare,reference_execute] at firstDone
    rw [ordinaryBare,reference_execute] at secondDone
    simp only [↓reduceIte,Option.getD_some,Outcome.done.injEq] at firstDone secondDone
    obtain ⟨rfl,_⟩ := firstDone
    obtain ⟨rfl,_⟩ := secondDone
    exact ⟨Iff.rfl,fun depth view => SourceCurrentOpenObservations.Same.refl depth view [replacement]⟩
  · exact warm_nonbare event free common current replacement available left right bare
      (fun found => bare ((SourceCurrentPublicationBareParity.bare event).mpr found)) firstDone secondDone

/-- Initial ready publication data constructs both actual filtered reconstruction schedules and their alignment. -/
theorem publication_binder_free [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (free : InternedStoredShallowCompletion.BinderFree event.expression)
    (common : State Symbol Guard) (current : Keeps event.afterBody common)
    (replacement : Value Symbol Guard) (available : Available common replacement) :
    ∃ left middle right reader,
      execute event.body
        (fun name => if name = .interned event.entry.identity then some replacement else none)
        common = .done left middle ∧
      execute event.ordinary
        (fun name => if name = .uninterned (ordinaryLevel event.depth) then some replacement else none)
        middle = .done right reader ∧
      execute event.body
        (fun name => if name = .interned event.entry.identity then some replacement else none)
        reader = .done left reader ∧
      execute event.ordinary
        (fun name => if name = .uninterned (ordinaryLevel event.depth) then some replacement else none)
        reader = .done right reader ∧
      Keeps common middle ∧ Keeps middle reader ∧ Available reader left ∧ Available reader right ∧
      Nonempty (History common middle) ∧ Nonempty (History middle reader) ∧ Related left right := by
  let bodyName : Reference := .interned event.entry.identity
  let ordinaryName : Reference := .uninterned (ordinaryLevel event.depth)
  let bodyMap : Environment Symbol Guard := fun name => if name = bodyName then some replacement else none
  let ordinaryMap : Environment Symbol Guard := fun name => if name = ordinaryName then some replacement else none
  obtain ⟨ordinaryEntry,cutContext,bodyEntry⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have bodyArgument : Available event.allocated (.reference bodyName) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have bodyContext := bodyEntry.base.local bodyName bodyArgument
  have bodyCallback : callback event.expression event.environment bodyName event.allocated =
      .done event.body event.afterBody := event.bodyDone
  have checked := callback_verified event.expression event.environment bodyName event.allocated
    bodyEntry.base.normal.facts bodyContext.inputs
  have bodyAvailable := checked.result event.body event.afterBody bodyCallback
  have ordinaryAvailableCut := (callback_verified event.expression event.environment ordinaryName event.afterDepth
    ordinaryEntry.base.normal.facts (ordinaryEntry.base.local ordinaryName (InternedNestedProvenance.ordinary_available _ _)).inputs).result
      event.ordinary event.cut event.ordinaryDone
  have ordinaryAvailableAllocated : Available event.allocated event.ordinary :=
    ordinaryAvailableCut.grows event.cut event.allocated
      ⟨extends_refl _,InternedBinderProtocol.intern_grows _ _,extends_refl _,extends_refl _⟩
      (InternedFreshProbeKeys.intern_issued_extends event.cut.nodes event.key cutContext.base.normal.facts.coherent.valid.2)
  have ordinaryAvailable : Available event.afterBody event.ordinary := by
    simpa only [bodyCallback,Outcome.state] using checked.available event.ordinary ordinaryAvailableAllocated
  have bodyReplacements : Replacements common bodyMap := by
    intro name value found
    dsimp only [bodyMap] at found
    split at found
    · cases found; exact available
    · cases found
  have ordinaryReplacements : Replacements common ordinaryMap := by
    intro name value found
    dsimp only [ordinaryMap] at found
    split at found
    · cases found; exact available
    · cases found
  obtain ⟨left,middle,firstDone,firstKept,leftAvailable,firstHistory⟩ :=
    SourceCurrentStoredReconstruction.execute event.body bodyMap common current.ready
      (current.available event.body bodyAvailable) bodyReplacements
  obtain ⟨right,reader,secondDone,secondKept,rightAvailable,secondHistory⟩ :=
    SourceCurrentStoredReconstruction.execute event.ordinary ordinaryMap middle firstKept.ready
      (firstKept.available event.ordinary (current.available event.ordinary ordinaryAvailable))
      (fun name value found => firstKept.available value (ordinaryReplacements name value found))
  have kept := firstKept.trans secondKept
  have firstWarm := InternedFreshOrdinaryReplay.build_replay (encode (leaves event.body) [] event.body)
    ((leaves event.body).map (InternedStoredSubstitution.input bodyMap)) common reader left middle
    current.ready.semantic.1.normal.facts.coherent.valid firstDone secondKept.growth
  have secondWarm := InternedFreshOrdinaryReplay.build_replay (encode (leaves event.ordinary) [] event.ordinary)
    ((leaves event.ordinary).map (InternedStoredSubstitution.input ordinaryMap)) middle reader right reader
    firstKept.ready.semantic.1.normal.facts.coherent.valid secondDone (grows_refl _)
  have related := warm event free reader (current.trans kept) replacement (kept.available replacement available)
    left right firstWarm secondWarm
  exact ⟨left,middle,right,reader,firstDone,secondDone,firstWarm,secondWarm,firstKept,secondKept,
    secondKept.available left leftAvailable,rightAvailable,firstHistory,secondHistory,related⟩

end MicroCFTA.SourceCurrentPublicationFilterAlignment
