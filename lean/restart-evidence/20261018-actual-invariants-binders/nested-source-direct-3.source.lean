import MicroCFTA.SourceCurrentNativeBinderExecution
import MicroCFTA.SourceCurrentNativeNormalizedComparisonExecution
import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.SourceCurrentNativeInputExchange

/-!
# Actual nested source binders with an inert local

Static free-name support excludes the supplied lexical argument.
The actual Depth callback makes the ordinary argument fresh for captures.
The raw ordinary result then needs no root filter or bare-self erasure.
Actual source history selects the earlier winner before smart cleanup.
-/
namespace MicroCFTA.SourceCurrentNestedSourceInertBinder
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work request finish)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (History)

/-- The pure source support has no contribution from the supplied local slot. -/
def Inert (body : Syntax Symbol Guard) (captures : List (Value Symbol Guard)) : Prop :=
  InternedProfileCallbackForm.usesArgument
    (InternedFreeNameForm.symbolic body (captures.map InternedRootProfile.profile) (captures.map Value.free)) = false

private theorem filter_absent [DecidableEq (EdgeKey Symbol Guard)]
    (name : Reference) (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) (absent : name ∉ value.free) :
    run (withoutSelfReference name value) state = (value,state) := by
  cases value with
  | empty | reference | node | mu => rfl
  | union entry members depth free =>
      have missing : Value.reference name ∉ members := by
        intro member
        apply absent
        rw [Value.free,InternedNormalizationFree.union_free state coherent entry members depth free available.resident,
          childFree_member]
        exact ⟨.reference name,member,by simp [Value.free]⟩
      rw [withoutSelfReference_absent name entry members depth free missing]
      rfl

/-- Actual Depth freshness and static support exclude the ordinary argument from the raw body result. -/
theorem raw_ordinary_absent [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (captures : List (Value Symbol Guard))
    (before afterDepth afterRaw : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context before captures)
    (inert : Inert body captures) (depth raw : Value Symbol Guard)
    (depthDone : callback body captures .depth before = .done depth afterDepth)
    (rawDone : build body (.reference (.uninterned (ordinaryLevel depth)) :: captures) afterDepth =
      .done raw afterRaw) :
    .uninterned (ordinaryLevel depth) ∉ raw.free := by
  have afterContext : InternedFreshOrdinaryContext.Context afterDepth captures := by
    simpa only [depthDone,Outcome.state] using context.callback body .depth (InternedNestedProvenance.depth_available before)
  have localContext := afterContext.local (.uninterned (ordinaryLevel depth))
    (InternedNestedProvenance.ordinary_available afterDepth (ordinaryLevel depth))
  have free := (InternedFreshOrdinaryFreeNames.build_free body _ afterDepth localContext.normal
    localContext.inputs localContext.freeNames localContext.profiles).result raw afterRaw rawDone
  intro present
  have supplied := (free (.uninterned (ordinaryLevel depth))).mp present
  simp only [List.map_cons,InternedRootProfile.profile,Value.free] at supplied
  rw [InternedFreeNameForm.supplied_member] at supplied
  rcases supplied with captured | ⟨used,_⟩
  · have observed := (InternedFreshOrdinarySourceFreeNames.callback_other body captures .depth before
      context.normal (context.local .depth (InternedNestedProvenance.depth_available before)).inputs
      context.freeNames context.profiles depth afterDepth depthDone
      (.uninterned (ordinaryLevel depth)) (by intro impossible; cases impossible)).mpr captured
    exact ordinary_fresh depth observed
  · rw [Inert] at inert
    rw [inert] at used
    cases used

private theorem source_keeps [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Value Symbol Guard))
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

/-- Initial causal data constructs the smart binder and its unchanged raw ordinary result. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (captures : List (Value Symbol Guard))
    (before : State Symbol Guard) (ready : Ready before) (available : Values before captures)
    (past : History empty before) (inert : Inert body captures) :
    ∃ depth afterDepth raw afterRaw after,
      callback body captures .depth before = .done depth afterDepth ∧
      build body (.reference (.uninterned (ordinaryLevel depth)) :: captures) afterDepth = .done raw afterRaw ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) afterRaw = (raw,afterRaw) ∧
      callback body captures (.uninterned (ordinaryLevel depth)) afterDepth = .done raw afterRaw ∧
      build (.binder true body) captures before = .done raw after ∧
      request true depth raw (callback body captures) afterRaw = .done raw after ∧
      .uninterned (ordinaryLevel depth) ∉ raw.free ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth raw = false ∧
      Keeps before after ∧ Available after raw ∧
      Nonempty (History before after) ∧ Nonempty (History empty after) := by
  have base := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic captures available
  have context : SourceCurrentConstrainedCapSourceHistory.Context before captures := ⟨base,ready.semantic.2⟩
  obtain ⟨value,after,actual⟩ := InternedRecordDepthCompletion.source_complete (.binder true body) captures before
    base ready.semantic.2 ready.covered
  have kept := source_keeps (.binder true body) captures before after ready available value actual
  obtain ⟨localHistory⟩ := SourceCurrentNativeMuPublication.build_history (.binder true body) captures before context
  have localHistory : History before after := by simpa only [actual,Outcome.state] using localHistory
  have finalHistory : History empty after := .trans past localHistory
  obtain ⟨depth,afterDepth,ordinary,cut,raw,afterRaw,depthDone,ordinaryDone,called,
    depthContext,_cutContext,_finalContext,rawDone,filtered,rawContext,_growth,_issued,depthAvailable,ordinaryAvailable⟩ :=
    SourceCurrentNativeBinderExecution.decompose true body captures before value after context actual
  have absent := raw_ordinary_absent body captures before afterDepth afterRaw base inert depth raw depthDone rawDone
  have rawAvailable := (InternedFreshOrdinaryFacts.build_verified body _ afterDepth
    depthContext.base.normal.facts (depthContext.local (.uninterned (ordinaryLevel depth))
      (InternedNestedProvenance.ordinary_available afterDepth (ordinaryLevel depth))).base.inputs).result raw afterRaw rawDone
  have unchanged := filter_absent (.uninterned (ordinaryLevel depth)) raw afterRaw
    rawContext.base.normal.facts.coherent rawAvailable absent
  have same := unchanged.symm.trans filtered
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
  have unused : InternedFreshOrdinaryDepthHeap.usesLocal depth raw = false := by
    simp only [InternedFreshOrdinaryDepthHeap.usesLocal,decide_eq_false_iff_not]
    intro member
    exact absent (InternedDeepFreeNormalization.deep_free raw after kept.ready.semantic.1.normal.facts.coherent
      ordinaryAvailable _ member)
  obtain ⟨entry,storedBody,present,returned⟩ := SourceCurrentNativeRequestProbes.request_probes true depth raw
    (callback body captures) afterRaw value after called kept.ready.semantic.1.normal.facts depthAvailable ordinaryAvailable
  have clean := SourceCurrentNativeNormalizedComparisonExecution.history_unused after finalHistory
    (muKey depth raw) entry storedBody depth raw present unused
  have notBare : raw.referenceOf ≠ .ref (.uninterned (ordinaryLevel depth)) := by
    intro same
    have equal := (referenceOf_self_iff _ raw).mp same
    exact absent (by rw [equal]; simp [Value.free])
  have sameValue : value = raw := returned.trans (clean.trans (by simp [SourceCurrentNativeCallbackErasure.eraseSelf,notBare]))
  rw [sameValue] at actual called
  exact ⟨depth,afterDepth,raw,afterRaw,after,depthDone,rawDone,unchanged,ordinaryDone,actual,called,
    absent,unused,kept,ordinaryAvailable,⟨localHistory⟩,⟨finalHistory⟩⟩

/-- Static inert support makes the actual filtered publication payloads literally equal. -/
theorem publication_eq [DecidableEq (EdgeKey Symbol Guard)]
    (event : SourceCurrentNativeMuPublication.Publication (Symbol := Symbol) (Guard := Guard))
    (inert : Inert event.expression event.environment) :
    event.body = event.ordinary ∧
      .uninterned (ordinaryLevel event.depth) ∉ event.body.free ∧
      .interned event.entry.identity ∉ event.body.free := by
  obtain ⟨rawOrdinary,afterRawOrdinary,rawBody,afterRawBody,ordinaryDone,ordinaryFilter,bodyDone,bodyFilter,
    ordinaryGrowth,bodyGrowth,ordinaryEntry,bodyEntry⟩ := SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  have ordinaryArgument := InternedNestedProvenance.ordinary_available event.afterDepth (ordinaryLevel event.depth)
  have ordinaryContext := ordinaryEntry.base.local (.uninterned (ordinaryLevel event.depth)) ordinaryArgument
  have ordinaryChecked := build_verified event.expression _ event.afterDepth ordinaryContext.normal.facts ordinaryContext.inputs
  have rawAvailable := ordinaryChecked.result rawOrdinary afterRawOrdinary ordinaryDone
  have rawContext : InternedFreshOrdinaryContext.Context afterRawOrdinary
      (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment) := by
    simpa only [ordinaryDone,Outcome.state] using ordinaryContext.build event.expression
  have absent := raw_ordinary_absent event.expression event.environment event.before event.afterDepth afterRawOrdinary
    event.context.base inert event.depth rawOrdinary event.depthDone ordinaryDone
  have unchanged := filter_absent (.uninterned (ordinaryLevel event.depth)) rawOrdinary afterRawOrdinary
    rawContext.normal.facts.coherent rawAvailable absent
  have same := unchanged.symm.trans ordinaryFilter
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
  have fresh : .interned event.entry.identity ∉ rawOrdinary.free := by
    have identity : event.entry.identity = event.cut.nodes.next :=
      InternedFreshProbeKeys.intern_miss_identity event.cut.nodes event.key event.missing
    rw [identity]
    exact InternedFreshProbeKeys.next_absent event.cut.nodes rawContext.normal.facts.coherent.valid.2
      rawOrdinary rawAvailable.issued
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have bodyArgument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have bodyContext := bodyEntry.base.local (.interned event.entry.identity) bodyArgument
  have bodyVerified := build_verified event.expression _ event.allocated bodyContext.normal.facts bodyContext.inputs
  have bodyAfter : InternedFreshOrdinaryContext.Context afterRawBody
      (.reference (.interned event.entry.identity) :: event.environment) := by
    simpa only [bodyDone,Outcome.state] using bodyContext.build event.expression
  have finalFacts := (callback_verified event.expression event.environment (.interned event.entry.identity)
    event.allocated bodyEntry.base.normal.facts bodyContext.inputs).facts
  have bodyCallback : callback event.expression event.environment (.interned event.entry.identity) event.allocated =
      .done event.body event.afterBody := event.bodyDone
  have coherent : Coherent event.afterBody := by
    simpa only [bodyCallback,Outcome.state] using finalFacts.coherent
  let inputs : List (Sum (Value Symbol Guard) Unit) := .inr () :: event.environment.map Sum.inl
  have instantiate (name : Reference) :
      inputs.map (InternedFreshOrdinaryLiveInputs.input (fun _ => name)) = .reference name :: event.environment := by
    simp [inputs,InternedFreshOrdinaryLiveInputs.input,List.map_map,Function.comp_def]
  have rawSame : rawOrdinary = rawBody := by
    apply SourceCurrentNativeInputExchange.of_completed event.expression inputs
      (fun _ => .uninterned (ordinaryLevel event.depth)) (fun _ => .interned event.entry.identity)
      event.afterDepth event.cut event.allocated afterRawBody event.afterBody
      (by simpa only [instantiate] using ordinaryContext) (by simpa only [instantiate] using bodyContext)
      coherent rawOrdinary rawBody (by simpa only [instantiate] using ordinaryDone)
      (by simpa only [instantiate] using bodyDone) (fun _ _ => absent) ordinaryGrowth bodyGrowth
  have bodyAvailable := bodyVerified.result rawBody afterRawBody bodyDone
  have bodyUnchanged := filter_absent (.interned event.entry.identity) rawBody afterRawBody bodyAfter.normal.facts.coherent
    bodyAvailable (rawSame ▸ fresh)
  have selected := (Prod.mk.inj (bodyUnchanged.symm.trans bodyFilter)).1
  exact ⟨selected.symm.trans rawSame.symm,by simpa only [← selected,← rawSame] using absent,
    by simpa only [← selected,← rawSame] using fresh⟩

/-- An actual inert publication constructs both exact reconstruction schedules without a BinderFree premise. -/
theorem publication_inert [DecidableEq (EdgeKey Symbol Guard)]
    (event : SourceCurrentNativeMuPublication.Publication (Symbol := Symbol) (Guard := Guard))
    (inert : Inert event.expression event.environment)
    (common : State Symbol Guard) (current : Keeps event.afterBody common)
    (replacement : Value Symbol Guard) (available : Available common replacement) :
    event.body = event.ordinary ∧
    ∃ result after,
      InternedFreshOrdinaryStoredSubstitution.execute event.body
        (fun name => if name = .interned event.entry.identity then some replacement else none) common = .done result after ∧
      InternedFreshOrdinaryStoredSubstitution.execute event.ordinary
        (fun name => if name = .uninterned (ordinaryLevel event.depth) then some replacement else none) after = .done result after ∧
      InternedFreshOrdinaryStoredSubstitution.execute event.body
        (fun name => if name = .interned event.entry.identity then some replacement else none) after = .done result after ∧
      Keeps common after ∧ Available after result ∧ Nonempty (History common after) := by
  obtain ⟨same,ordinaryAbsent,bodyAbsent⟩ := publication_eq event inert
  have bodyEntry := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.2
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have bodyArgument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have bodyContext := bodyEntry.base.local (.interned event.entry.identity) bodyArgument
  have called : callback event.expression event.environment (.interned event.entry.identity) event.allocated =
      .done event.body event.afterBody := event.bodyDone
  have bodyAvailable := (callback_verified event.expression event.environment (.interned event.entry.identity)
    event.allocated bodyEntry.base.normal.facts bodyContext.inputs).result event.body event.afterBody called
  let bodyMap : InternedStoredSubstitution.Environment Symbol Guard :=
    fun name => if name = .interned event.entry.identity then some replacement else none
  let ordinaryMap : InternedStoredSubstitution.Environment Symbol Guard :=
    fun name => if name = .uninterned (ordinaryLevel event.depth) then some replacement else none
  have replacements : InternedStoredSubstitution.Replacements common bodyMap := by
    intro name value found
    dsimp only [bodyMap] at found
    split at found
    · cases found; exact available
    · cases found
  obtain ⟨result,after,firstDone,kept,resultAvailable,history⟩ :=
    SourceCurrentStoredReconstruction.execute event.body bodyMap common current.ready
      (current.available _ bodyAvailable) replacements
  have warm := InternedFreshOrdinaryReplay.build_replay
    (InternedStoredSubstitution.encode (InternedStoredSubstitution.leaves event.body) [] event.body)
    ((InternedStoredSubstitution.leaves event.body).map (InternedStoredSubstitution.input bodyMap))
    common after result after current.ready.semantic.1.normal.facts.coherent.valid firstDone (grows_refl _)
  have maps := InternedFreshOrdinaryStoredSubstitution.execute_congr event.body bodyMap ordinaryMap after
    kept.ready.semantic.1.normal.facts.coherent (kept.available _ (current.available _ bodyAvailable)) (by
      intro name member
      have left : name ≠ .interned event.entry.identity := fun equal => bodyAbsent (equal ▸ member)
      have right : name ≠ .uninterned (ordinaryLevel event.depth) := fun equal => ordinaryAbsent (equal ▸ member)
      simp only [bodyMap,ordinaryMap,left,right,ite_false])
  refine ⟨same,result,after,firstDone,?_,warm,kept,resultAvailable,history⟩
  rw [← same,← maps]
  exact warm

end MicroCFTA.SourceCurrentNestedSourceInertBinder
