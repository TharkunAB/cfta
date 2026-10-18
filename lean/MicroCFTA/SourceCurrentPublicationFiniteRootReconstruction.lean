import MicroCFTA.SourceCurrentFiniteRootReconstruction
import MicroCFTA.SourceCurrentPublicationSharedReplacements
import MicroCFTA.SourceCurrentRetainedMuWriterAlignment

/-!
# Finite reconstruction of actual publication roots

The induction hypothesis applies only to the actual immediate binder body.
Both raw callback return heaps must grow into the execution heap.
The two filtered callbacks use one sparse replacement map. Actual stored
calls run in sequence and replay at their final execution heap. Finite
observations use a fixed, separate reader. A literal Mu atom retains the
strict body reconstruction obligation. This module does not discharge it.
-/
namespace MicroCFTA.SourceCurrentPublicationFiniteRootReconstruction
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedStoredSubstitution (Environment Replacements leaves encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedFreshOrdinaryLiveInputs (input liftInput local_inputs)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentNativeMuPublication (Publication History)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentUsedBinderAliasTransport (Aliases NamePair)
open SourceCurrentUsedBinderRootAlternatives (RootMatch AtomMatch)
open SourceCurrentFiniteRootReconstruction (Executions)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt)
open SourceCurrentPublicationSharedReplacements (shared)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceCurrentRetainedMuWriterAlignment (Writer)

private theorem bind_replacements (state : State Symbol Guard) (name : Reference)
    (value : Value Symbol Guard) (available : Available state value)
    (environment : Environment Symbol Guard) (replacements : Replacements state environment) :
    Replacements state (bind name value environment) := by
  intro queried output found
  dsimp only [SourceCurrentStoredMuBinderChildLineage.bind] at found
  split at found
  · cases found; exact available
  · exact replacements queried output found

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual body supplies root matches when both raw returns grow into the execution heap. -/
def BodyIH (depth : Nat) (view : State Symbol Guard)
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (replacement : Value Symbol Guard) (environment : Environment Symbol Guard)
    (common : State Symbol Guard) : Prop :=
  ∀ execution, Keeps common execution →
  let localInputs := .inr (.inl ()) ::
    (event.environment.map (fun value => (Sum.inl value : Sum (Value Symbol Guard) Unit))).map liftInput
  let firstNames := Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) (fun _ : Unit => .depth)
  let secondNames := Sum.elim (fun _ : Unit => .interned event.entry.identity) (fun _ : Unit => .depth)
  sizeOf event.expression < sizeOf (.binder event.smart event.expression : Syntax Symbol Guard) →
  Aliases event.expression localInputs firstNames secondNames →
  ∀ before later, Context before (localInputs.map (input firstNames)) →
    Context later (localInputs.map (input secondNames)) →
  ∀ rawFirst rawHeap rawSecond rawLater,
    build event.expression (localInputs.map (input firstNames)) before = .done rawFirst rawHeap →
    build event.expression (localInputs.map (input secondNames)) later = .done rawSecond rawLater →
    Grows rawHeap execution → Grows rawLater execution →
    RootMatch (NamePair (.uninterned (ordinaryLevel event.depth)) (.interned event.entry.identity))
      (Executions (depth + 1) view execution (shared event replacement replacement environment)
        (shared event replacement replacement environment)) rawFirst rawSecond

private theorem output_context
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before after : State Symbol Guard) (context : Context before environment) (value : Value Symbol Guard)
    (actual : build expression environment before = .done value after) :
    Context after environment ∧ Available after value := by
  exact ⟨by simpa only [actual, Outcome.state] using context.build expression,
    (build_verified expression environment before context.normal.facts context.inputs).result value after actual⟩

private theorem filtered
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (execution : State Symbol Guard) (growth : Grows event.afterBody execution)
    (references : Reference → Reference → Prop) (values : Value Symbol Guard → Value Symbol Guard → Prop)
    (referenceLocal : ∀ first second, references first second →
      (first = .uninterned (ordinaryLevel event.depth) ↔ second = .interned event.entry.identity))
    (strict :
      let localInputs := .inr (.inl ()) ::
        (event.environment.map (fun value => (Sum.inl value : Sum (Value Symbol Guard) Unit))).map liftInput
      let firstNames := Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) (fun _ : Unit => .depth)
      let secondNames := Sum.elim (fun _ : Unit => .interned event.entry.identity) (fun _ : Unit => .depth)
      sizeOf event.expression < sizeOf (.binder event.smart event.expression : Syntax Symbol Guard) →
      Aliases event.expression localInputs firstNames secondNames →
      ∀ before later, Context before (localInputs.map (input firstNames)) →
        Context later (localInputs.map (input secondNames)) →
      ∀ rawFirst rawHeap rawSecond rawLater,
        build event.expression (localInputs.map (input firstNames)) before = .done rawFirst rawHeap →
        build event.expression (localInputs.map (input secondNames)) later = .done rawSecond rawLater →
        Grows rawHeap execution → Grows rawLater execution →
        RootMatch references values rawFirst rawSecond) :
    RootMatch references values event.ordinary event.body := by
  let inputs : List (Sum (Value Symbol Guard) Unit) := event.environment.map Sum.inl
  let names : Unit → Reference := fun _ => .depth
  let localInputs := .inr (.inl ()) :: inputs.map liftInput
  let firstNames := Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) names
  let secondNames := Sum.elim (fun _ : Unit => .interned event.entry.identity) names
  change sizeOf event.expression < sizeOf (.binder event.smart event.expression : Syntax Symbol Guard) →
    Aliases event.expression localInputs firstNames secondNames →
    ∀ before later, Context before (localInputs.map (input firstNames)) →
      Context later (localInputs.map (input secondNames)) →
    ∀ rawFirst rawHeap rawSecond rawLater,
      build event.expression (localInputs.map (input firstNames)) before = .done rawFirst rawHeap →
      build event.expression (localInputs.map (input secondNames)) later = .done rawSecond rawLater →
      Grows rawHeap execution → Grows rawLater execution →
      RootMatch references values rawFirst rawSecond at strict
  have fixed : inputs.map (input names) = event.environment := by
    simp [inputs,input,List.map_map,Function.comp_def]
  have instantiated (own : Reference) :
      localInputs.map (input (Sum.elim (fun _ : Unit => own) names)) = .reference own :: event.environment := by
    rw [local_inputs,fixed]
  obtain ⟨rawFirst,rawHeap,rawSecond,rawLater,firstRaw,firstFilter,secondRaw,secondFilter,firstGrowth,secondGrowth,firstEntry,secondEntry⟩ :=
    SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have bodyArgument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have firstContext := firstEntry.base.local (.uninterned (ordinaryLevel event.depth))
    (InternedNestedProvenance.ordinary_available _ _)
  have secondContext := secondEntry.base.local (.interned event.entry.identity) bodyArgument
  have rawMatch := strict (by simp) (SourceCurrentUsedBinderAliasTransport.publication event)
    event.afterDepth event.allocated
    (by simpa only [firstNames,instantiated] using firstContext)
    (by simpa only [secondNames,instantiated] using secondContext)
    rawFirst rawHeap rawSecond rawLater
    (by simpa only [firstNames,instantiated] using firstRaw)
    (by simpa only [secondNames,instantiated] using secondRaw)
    (grows_trans firstGrowth growth) (grows_trans secondGrowth growth)
  have firstReturned := output_context event.expression _ event.afterDepth rawHeap firstContext rawFirst firstRaw
  have secondReturned := output_context event.expression _ event.allocated rawLater secondContext rawSecond secondRaw
  have rawBare : rawFirst = .reference (.uninterned (ordinaryLevel event.depth)) ↔
      rawSecond = .reference (.interned event.entry.identity) := by
    have firstSelf := InternedFilterSelfReference.filter_self_iff (.uninterned (ordinaryLevel event.depth)) rawFirst rawHeap
      firstReturned.1.normal.facts.coherent firstReturned.1.normal.flat firstReturned.2
    have secondSelf := InternedFilterSelfReference.filter_self_iff (.interned event.entry.identity) rawSecond rawLater
      secondReturned.1.normal.facts.coherent secondReturned.1.normal.flat secondReturned.2
    rw [firstFilter] at firstSelf
    rw [secondFilter] at secondSelf
    exact firstSelf.symm.trans ((SourceCurrentPublicationBareParity.bare event).symm.trans secondSelf)
  have filtered := SourceCurrentUsedBinderRootAlternatives.filter references values _ _ rawFirst rawSecond rawHeap rawLater
    firstReturned.1.normal secondReturned.1.normal firstReturned.2 secondReturned.2 rawMatch referenceLocal rawBare
  rw [firstFilter,secondFilter] at filtered
  exact filtered


private theorem callback_available (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    Available event.afterBody event.body ∧ Available event.afterBody event.ordinary := by
  let bodyName : Reference := .interned event.entry.identity
  let ordinaryName : Reference := .uninterned (ordinaryLevel event.depth)
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
  exact ⟨bodyAvailable,by
    simpa only [bodyCallback,Outcome.state] using checked.available event.ordinary ordinaryAvailableAllocated⟩

/-- Actual publication callbacks construct both stored calls and retain finite root observations. -/
theorem publication (depth : Nat) (view : State Symbol Guard)
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (common : State Symbol Guard) (current : Keeps event.afterBody common)
    (replacement : Value Symbol Guard) (available : Available common replacement)
    (environment : Environment Symbol Guard) (replacements : Replacements common environment)
    (strict : BodyIH depth view event replacement environment common) :
    ∃ left middle right final,
      execute event.body (bind (.interned event.entry.identity) replacement environment) common = .done left middle ∧
      execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) replacement environment) middle = .done right final ∧
      execute event.body (bind (.interned event.entry.identity) replacement environment) final = .done left final ∧
      execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) replacement environment) final = .done right final ∧
      Keeps common middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Nonempty (History common middle) ∧ Nonempty (History middle final) ∧ RelatedAt (depth + 1) view left right := by
  let bodyName : Reference := .interned event.entry.identity
  let ordinaryName : Reference := .uninterned (ordinaryLevel event.depth)
  let bodyMap := bind bodyName replacement environment
  let ordinaryMap := bind ordinaryName replacement environment
  let commonMap := shared event replacement replacement environment
  obtain ⟨bodyAvailable,ordinaryAvailable⟩ := callback_available event
  have bodyReplacements := bind_replacements common bodyName replacement available environment replacements
  have ordinaryReplacements := bind_replacements common ordinaryName replacement available environment replacements
  obtain ⟨left,middle,firstDone,firstKept,leftAvailable,firstHistory⟩ :=
    SourceCurrentStoredReconstruction.execute event.body bodyMap common current.ready
      (current.available event.body bodyAvailable) bodyReplacements
  obtain ⟨right,final,secondDone,secondKept,rightAvailable,secondHistory⟩ :=
    SourceCurrentStoredReconstruction.execute event.ordinary ordinaryMap middle firstKept.ready
      (firstKept.available event.ordinary (current.available event.ordinary ordinaryAvailable))
      (fun name value found => firstKept.available value (ordinaryReplacements name value found))
  have kept := firstKept.trans secondKept
  have finalCurrent := current.trans kept
  have finalBody := finalCurrent.available event.body bodyAvailable
  have finalOrdinary := finalCurrent.available event.ordinary ordinaryAvailable
  have firstWarm := InternedFreshOrdinaryReplay.build_replay (encode (leaves event.body) [] event.body)
    ((leaves event.body).map (InternedStoredSubstitution.input bodyMap)) common final left middle
    current.ready.semantic.1.normal.facts.coherent.valid firstDone secondKept.growth
  have secondWarm := InternedFreshOrdinaryReplay.build_replay (encode (leaves event.ordinary) [] event.ordinary)
    ((leaves event.ordinary).map (InternedStoredSubstitution.input ordinaryMap)) middle final right final
    firstKept.ready.semantic.1.normal.facts.coherent.valid secondDone (grows_refl _)
  have referenceLocal : ∀ first second, NamePair ordinaryName bodyName first second →
      (first = ordinaryName ↔ second = bodyName) := by
    intro first second paired
    rcases paired with ⟨rfl,rfl⟩ | ⟨_,different,other⟩
    · exact ⟨fun _ => rfl,fun _ => rfl⟩
    · exact iff_of_false different other
  have matched := filtered event final finalCurrent.growth (NamePair ordinaryName bodyName)
    (Executions (depth + 1) view final commonMap commonMap) referenceLocal (strict final kept)
  have resolved : ∀ first second, NamePair ordinaryName bodyName first second →
      RelatedAt (depth + 1) view ((commonMap first).getD (.reference first))
        ((commonMap second).getD (.reference second)) := by
    intro first second paired
    rcases paired with ⟨rfl,rfl⟩ | ⟨rfl,_,_⟩
    · have same : (commonMap ordinaryName).getD (.reference ordinaryName) = replacement ∧
          (commonMap bodyName).getD (.reference bodyName) = replacement := by
        simp only [commonMap,shared,SourceCurrentStoredMuBinderChildLineage.bind,bodyName,ordinaryName,
          reduceCtorEq,ite_false,ite_true,Option.getD_some]
        exact ⟨trivial,trivial⟩
      rw [same.1,same.2]
      exact ⟨Iff.rfl,SourceCurrentOpenObservations.Same.refl _ _ _⟩
    · exact ⟨Iff.rfl,SourceCurrentOpenObservations.Same.refl _ _ _⟩
  have commonReplacements : Replacements final commonMap :=
    bind_replacements final bodyName replacement (kept.available replacement available) _
      (bind_replacements final ordinaryName replacement (kept.available replacement available) environment
        (fun name value found => kept.available value (replacements name value found)))
  have reconstructed := SourceCurrentFiniteRootReconstruction.reconstruct depth view final
    (NamePair ordinaryName bodyName) (Executions (depth + 1) view final commonMap commonMap)
    commonMap commonMap event.ordinary event.body secondKept.ready finalOrdinary finalBody
    commonReplacements commonReplacements matched resolved
    (by
      intro first second _ _ atom
      cases first <;> cases second <;> try {cases atom}
      exact atom)
    (by
      intro first second related left right firstCall secondCall
      have observed := related left right firstCall secondCall
      exact ⟨observed.1,observed.2.lower⟩)
  have substitutions := SourceCurrentPublicationSharedReplacements.substitutions event replacement replacement environment
    final secondKept.ready.semantic.1.normal.facts.coherent finalBody finalOrdinary
  have related := reconstructed right left (substitutions.2 ▸ secondWarm) (substitutions.1 ▸ firstWarm)
  exact ⟨left,middle,right,final,firstDone,secondDone,firstWarm,secondWarm,firstKept,secondKept,
    secondKept.available left leftAvailable,rightAvailable,firstHistory,secondHistory,related.1.symm,related.2.symm⟩

/-- An installed earlier writer retains its exact record and both actual reconstructed results. -/
theorem writer (depth : Nat) (view common : State Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body cachedDepth ordinary : Value Symbol Guard)
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (past : Writer common key (.mu entry body cachedDepth ordinary) event)
    (ready : Ready common) (selected : common.nodeRecords key = some (.mu entry body cachedDepth ordinary))
    (replacement : Value Symbol Guard) (available : Available common replacement)
    (environment : Environment Symbol Guard) (replacements : Replacements common environment)
    (strict : BodyIH depth view event replacement environment common) :
    ∃ left middle right final,
      execute body (bind (.interned entry.identity) replacement environment) common = .done left middle ∧
      execute ordinary (bind (.uninterned (ordinaryLevel cachedDepth)) replacement environment) middle = .done right final ∧
      execute body (bind (.interned entry.identity) replacement environment) final = .done left final ∧
      execute ordinary (bind (.uninterned (ordinaryLevel cachedDepth)) replacement environment) final = .done right final ∧
      Keeps common middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Nonempty (History common middle) ∧ Nonempty (History middle final) ∧
      final.nodeRecords key = some (.mu entry body cachedDepth ordinary) ∧ RelatedAt (depth + 1) view left right := by
  obtain ⟨_,same,_,_,_,_,_,growth,issued⟩ := past
  change Value.mu entry body cachedDepth ordinary = Value.mu event.entry event.body event.depth event.ordinary at same
  obtain ⟨rfl,rfl,rfl,rfl⟩ := Value.mu.inj same
  obtain ⟨left,middle,right,final,firstDone,secondDone,firstWarm,secondWarm,firstKept,secondKept,
    leftAvailable,rightAvailable,firstHistory,secondHistory,related⟩ :=
    publication depth view event common ⟨ready,growth,issued⟩ replacement available environment replacements strict
  exact ⟨left,middle,right,final,firstDone,secondDone,firstWarm,secondWarm,firstKept,secondKept,
    leftAvailable,rightAvailable,firstHistory,secondHistory,
    secondKept.growth.nodeRecords key _ (firstKept.growth.nodeRecords key _ selected),related⟩

end MicroCFTA.SourceCurrentPublicationFiniteRootReconstruction
