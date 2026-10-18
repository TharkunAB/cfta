import MicroCFTA.SourceCurrentTrackedFilteredFusion
import MicroCFTA.SourceCurrentNativeMuIssuedWriters
import MicroCFTA.SourceCurrentBinderFusionInduction
import MicroCFTA.SourceCurrentPublicationSharedReplacements

/-!
# Smaller original-depth fusion at actual selected writers

Actual histories retain the original writer and its complete captures.
A smaller-depth source hypothesis compares its body and ordinary probe
under arbitrary outer replacements. Local replacements retain a finite
tracked root profile. The comparison retains Empty and bare tracked names.
The uniform induction and the full binder case remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentTrackedWriterFusion
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedFreshOrdinaryLiveInputs (input liftInput local_inputs)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedWriters (Written)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentPublicationSharedReplacements (shared)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentTrackedFilteredFusion (Fusion)
open SourceCurrentTrackedRootProfile (Related)

private theorem scope_body (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (label : Sum Reference (Sum Unit Atom))
    (member : label ∈ Scope body (.inr (.inl ()) :: inputs.map liftInput)) :
    label = .inr (.inl ()) ∨ ∃ old ∈ Scope (.binder true body) inputs,
      label = InternedFreshOrdinaryLiveInputs.liftName (.inr old) := by
  rcases List.mem_cons.mp member with rfl | member
  · exact Or.inr ⟨.inl .depth,List.mem_cons_self,rfl⟩
  · cases label with
    | inl name =>
        exact Or.inr ⟨.inl name,List.mem_cons_of_mem _
          ((SourceCurrentNativeNormalizedComparison.capture_support body inputs (.inl name)).mp member),rfl⟩
    | inr selected =>
        cases selected with
        | inl token => cases token; exact Or.inl rfl
        | inr atom =>
            exact Or.inr ⟨.inr atom,List.mem_cons_of_mem _
              ((SourceCurrentNativeNormalizedComparison.capture_support body inputs (.inr atom)).mp member),rfl⟩


variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem same_inputs (event : Publication (Symbol := Symbol) (Guard := Guard))
    (own : Reference) :
    (.inr (.inl ()) :: (event.environment.map (fun value => (Sum.inl value : Sum (Value Symbol Guard) Unit))).map liftInput).map
      (input (Sum.elim (fun _ : Unit => own) (fun _ : Unit => .depth))) = .reference own :: event.environment := by
  rw [local_inputs]
  simp [input,List.map_map,Function.comp_def]

private theorem publication_tests (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    let inputs := .inr (.inl ()) ::
      (event.environment.map (fun value => (Sum.inl value : Sum (Value Symbol Guard) Unit))).map liftInput
    let firstNames : Sum Unit Unit → Reference := Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) (fun _ : Unit => .depth)
    let secondNames : Sum Unit Unit → Reference := Sum.elim (fun _ : Unit => .interned event.entry.identity) (fun _ : Unit => .depth)
    ∀ label ∈ Scope event.expression inputs,
      Sum.elim id firstNames label = .uninterned (ordinaryLevel event.depth) ↔
        Sum.elim id secondNames label = .interned event.entry.identity := by
  let captures : List (Sum (Value Symbol Guard) Unit) := event.environment.map Sum.inl
  let names : Unit → Reference := fun _ => .depth
  have fixed : captures.map (input names) = event.environment := by
    simp [captures,input,List.map_map,Function.comp_def]
  have ordinaryFresh := SourceCurrentNativeNormalizationFreshness.ordinary event.expression captures names
    event.before event.afterDepth (by simpa only [fixed] using event.context.base)
    event.depth (by simpa only [fixed] using event.depthDone)
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have reservedFresh := SourceCurrentNativeNormalizationFreshness.reserved (.binder true event.expression)
    captures names event.cut (by simpa only [fixed] using cutContext.base) event.key event.missing
  have fresh :
      .uninterned (ordinaryLevel event.depth) ∉ (Scope (.binder true event.expression) captures).map (Sum.elim id names) ∧
      .interned event.entry.identity ∉ (Scope (.binder true event.expression) captures).map (Sum.elim id names) := by
    constructor
    · simpa only [Scope,List.map_cons,Sum.elim_inl,id_eq,List.mem_cons,reduceCtorEq,false_or] using ordinaryFresh
    · simpa only [Scope,List.map_cons,Sum.elim_inl,id_eq,List.mem_cons,reduceCtorEq,false_or,Publication.entry] using reservedFresh
  dsimp only
  intro label member
  rcases scope_body event.expression captures label member with rfl | ⟨old,present,rfl⟩
  · exact ⟨fun _ => rfl,fun _ => rfl⟩
  · have supplied (own : Reference) :
        Sum.elim id (Sum.elim (fun _ : Unit => own) names)
          (InternedFreshOrdinaryLiveInputs.liftName (.inr old)) = Sum.elim id names old := by
      cases old <;> rfl
    change Sum.elim id (Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) names)
        (InternedFreshOrdinaryLiveInputs.liftName (.inr old)) = _ ↔
      Sum.elim id (Sum.elim (fun _ : Unit => .interned event.entry.identity) names)
        (InternedFreshOrdinaryLiveInputs.liftName (.inr old)) = _
    rw [supplied,supplied]
    exact iff_of_false (fun same => fresh.1 (List.mem_map.mpr ⟨old,present,same⟩))
      (fun same => fresh.2 (List.mem_map.mpr ⟨old,present,same⟩))

private theorem callback_replay
    (expression : InternedNestedConstruction.Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (own : Reference) (before after reader : State Symbol Guard)
    (context : Context before (.reference own :: environment)) (filtered : Value Symbol Guard)
    (actual : InternedFreshOrdinaryFacts.callback expression environment own before = .done filtered after)
    (current : Keeps after reader) :
    ∃ raw middle,
      build expression (.reference own :: environment) before = .done raw middle ∧
      run (withoutSelfReference own raw) middle = (filtered,after) ∧
      Context reader (.reference own :: environment) ∧ Keeps middle reader ∧
      Available reader raw ∧
      build expression (.reference own :: environment) reader = .done raw reader ∧
      run (withoutSelfReference own raw) reader = (filtered,reader) := by
  obtain ⟨raw,middle,built,cut⟩ := SourceCurrentNativeMuPublicationCallbacks.callback_raw expression environment own before filtered after actual
  have checked := build_verified expression _ before context.base.normal.facts context.base.inputs
  have returned : Context middle (.reference own :: environment) := by
    simpa only [built,Outcome.state] using context.build expression
  have available := checked.result raw middle built
  have filteredChecked := InternedNestedFacts.filter_verified own raw middle returned.base.normal.facts available
  have filterGrowth : Grows middle after := by
    simpa only [work,cut,Outcome.state] using filteredChecked.growth
  have filterIssued : Extends middle.nodes.issued after.nodes.issued := by
    simpa only [work,cut,Outcome.state] using filteredChecked.history
  have whole : Keeps middle reader :=
    ⟨current.ready,grows_trans filterGrowth current.growth,extends_trans filterIssued current.history⟩
  obtain ⟨readerContext,_,warm⟩ := SourceCurrentGeneratedHistoricalContext.replay expression _ before middle reader
    context raw built whole
  have filterWarm : run (withoutSelfReference own raw) reader = (filtered,reader) := by
    simpa only [cut] using replay (withoutSelfReference own raw) middle reader returned.base.normal.facts.coherent.valid
      (by rw [cut]; exact current.growth)
  exact ⟨raw,middle,built,cut,readerContext,whole,whole.available raw available,warm,filterWarm⟩

private theorem filtered_available (reader : State Symbol Guard) (ready : Ready reader)
    (raw filtered : Value Symbol Guard) (own : Reference) (available : Available reader raw)
    (actual : run (withoutSelfReference own raw) reader = (filtered,reader)) : Available reader filtered := by
  apply (InternedNestedFacts.filter_verified own raw reader ready.semantic.1.normal.facts available).result filtered reader
  simp only [work,actual]

private theorem shared_replacements (event : Publication (Symbol := Symbol) (Guard := Guard))
    (firstValue secondValue : Value Symbol Guard) (environment : Environment Symbol Guard)
    (reader : State Symbol Guard) (first : Available reader firstValue) (second : Available reader secondValue)
    (replacements : Replacements reader environment) : Replacements reader (shared event firstValue secondValue environment) := by
  intro name value found
  dsimp only [shared,SourceCurrentStoredMuBinderChildLineage.bind] at found
  split at found
  · cases found; exact first
  · split at found
    · cases found; exact second
    · exact replacements name value found

/-- Actual callback histories apply a smaller original-depth source law under arbitrary outer replacements. -/
theorem publication (markers : List Reference) (event : Publication (Symbol := Symbol) (Guard := Guard)) (reader : State Symbol Guard)
    (ordinaryCurrent : Keeps event.cut reader) (bodyCurrent : Keeps event.afterBody reader)
    (smaller : Fusion event.body.depth event.expression)
    (firstValue secondValue : Value Symbol Guard) (environment : Environment Symbol Guard)
    (firstAvailable : Available reader firstValue) (secondAvailable : Available reader secondValue)
    (replacements : Replacements reader environment)
    (related : Related markers firstValue secondValue)
    (left right : Value Symbol Guard)
    (bodyDone : execute event.body (bind (.interned event.entry.identity) firstValue environment)
      reader = .done left reader)
    (ordinaryDone : execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) secondValue environment)
      reader = .done right reader) :
    Related markers left right := by
  have ready := bodyCurrent.ready
  obtain ⟨ordinaryEntry,cutEntry,bodyEntry⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have ordinaryContext := ordinaryEntry.local (.uninterned (ordinaryLevel event.depth))
    (InternedNestedProvenance.ordinary_available _ _)
  have bodyArgument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutEntry.base.normal.facts.coherent
      cutEntry.base.normal.facts.cached).2
  have bodyContext := bodyEntry.local (.interned event.entry.identity) bodyArgument
  obtain ⟨rawOrdinary,ordinaryHeap,ordinaryBuild,ordinaryFilter,ordinaryReader,ordinaryKept,ordinaryAvailable,ordinaryWarm,ordinaryFilterWarm⟩ :=
    callback_replay event.expression event.environment (.uninterned (ordinaryLevel event.depth)) event.afterDepth event.cut reader
      ordinaryContext event.ordinary event.ordinaryDone ordinaryCurrent
  obtain ⟨rawBody,bodyHeap,bodyBuild,bodyFilter,bodyReader,bodyKept,bodyAvailable,bodyWarm,bodyFilterWarm⟩ :=
    callback_replay event.expression event.environment (.interned event.entry.identity) event.allocated event.afterBody reader
      bodyContext event.body event.bodyDone bodyCurrent
  obtain ⟨rankOrdinary,rankOrdinaryHeap,rankBody,rankBodyHeap,rankOrdinaryBuild,_rankOrdinaryFilter,
    rankBodyBuild,_rankBodyFilter,_rankOrdinaryContext,_rankBodyContext,_rankOrdinaryGrowth,_rankBodyGrowth,
    ordinaryDepth,bodyDepth,sameDepth,_probeDepth,_ordinaryLess,_bodyLess⟩ :=
    SourceCurrentBinderFusionInduction.publication event
  have ordinarySame : rankOrdinary = rawOrdinary := (Outcome.done.inj (rankOrdinaryBuild.symm.trans ordinaryBuild)).1
  have bodySame : rankBody = rawBody := (Outcome.done.inj (rankBodyBuild.symm.trans bodyBuild)).1
  rw [ordinarySame] at ordinaryDepth
  rw [bodySame] at bodyDepth
  have ordinaryBound : rawOrdinary.depth ≤ event.body.depth := by omega
  have bodyBound : rawBody.depth ≤ event.body.depth := by omega
  let localInputs := .inr (.inl ()) ::
    (event.environment.map (fun value => (Sum.inl value : Sum (Value Symbol Guard) Unit))).map liftInput
  let ordinaryNames : Sum Unit Unit → Reference :=
    Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) (fun _ : Unit => .depth)
  let bodyNames : Sum Unit Unit → Reference :=
    Sum.elim (fun _ : Unit => .interned event.entry.identity) (fun _ : Unit => .depth)
  let maps := shared event firstValue secondValue environment
  have substitutions := SourceCurrentPublicationSharedReplacements.substitutions event firstValue secondValue environment reader
    ready.semantic.1.normal.facts.coherent
    (filtered_available reader ready rawBody event.body _ bodyAvailable bodyFilterWarm)
    (filtered_available reader ready rawOrdinary event.ordinary _ ordinaryAvailable ordinaryFilterWarm)
  have paired := SourceCurrentPublicationSharedReplacements.paired event
    (Related markers) (Related.refl markers)
    firstValue secondValue environment related
  have bodyAliases : Aliases event.expression localInputs bodyNames ordinaryNames := by
    intro first firstMember second secondMember
    exact (SourceCurrentUsedBinderAliasTransport.publication event first firstMember second secondMember).symm
  have tests : ∀ label ∈ Scope event.expression localInputs,
      Sum.elim id bodyNames label = .interned event.entry.identity ↔
      Sum.elim id ordinaryNames label = .uninterned (ordinaryLevel event.depth) :=
    fun label member => (publication_tests event label member).symm
  have mapsReady := shared_replacements event firstValue secondValue environment reader firstAvailable secondAvailable replacements
  exact smaller markers reader ready localInputs bodyNames ordinaryNames (.interned event.entry.identity)
    (.uninterned (ordinaryLevel event.depth)) maps maps reader reader reader reader
    rawBody rawOrdinary event.body event.ordinary left right bodyBound ordinaryBound
    (by simpa only [localInputs,bodyNames,same_inputs] using bodyReader)
    (by simpa only [localInputs,ordinaryNames,same_inputs] using ordinaryReader)
    bodyAliases tests (by simpa only [localInputs,bodyNames,ordinaryNames,same_inputs] using paired)
    mapsReady mapsReady bodyAvailable ordinaryAvailable
    (by simpa only [localInputs,bodyNames,same_inputs] using bodyWarm)
    (by simpa only [localInputs,ordinaryNames,same_inputs] using ordinaryWarm)
    (grows_refl _) (grows_refl _) bodyFilterWarm ordinaryFilterWarm
    (substitutions.1.symm.trans bodyDone) (substitutions.2.symm.trans ordinaryDone)

/-- A selected earlier writer consumes only the uniform induction hypothesis below its original depth. -/
theorem writer {before reader : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (written : Written before reader key value) (ready : Ready reader)
    (smaller : ∀ rank < value.depth, ∀ expression : Syntax Symbol Guard, Fusion rank expression) :
    ∃ event : Publication (Symbol := Symbol) (Guard := Guard),
      key = event.key ∧ value = event.candidate ∧ event.body.depth < value.depth ∧
      ∀ (markers : List Reference) (firstValue secondValue : Value Symbol Guard) (environment : Environment Symbol Guard),
        Available reader firstValue → Available reader secondValue → Replacements reader environment →
        Related markers firstValue secondValue →
        ∀ left right,
          execute event.body (bind (.interned event.entry.identity) firstValue environment) reader = .done left reader →
          execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) secondValue environment) reader = .done right reader →
          Related markers left right := by
  obtain ⟨event,sameKey,sameValue,_missing,_prefix,_depth,_ordinary,⟨bodyPath⟩,growth,issued⟩ := written
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have reserveIssued : Extends event.cut.nodes.issued event.allocated.nodes.issued :=
    InternedFreshProbeKeys.intern_issued_extends event.cut.nodes event.key cutContext.base.normal.facts.coherent.valid.2
  have cutCurrent : Keeps event.cut reader :=
    ⟨ready,grows_trans (SourceCurrentNativeMuGrowthHistory.reserve_growth event)
      (grows_trans bodyPath.growth (grows_trans (SourceCurrentNativeMuGrowthHistory.publication_growth event) growth)),
      extends_trans reserveIssued (extends_trans bodyPath.issued issued)⟩
  have bodyCurrent : Keeps event.afterBody reader :=
    ⟨ready,grows_trans (SourceCurrentNativeMuGrowthHistory.publication_growth event) growth,issued⟩
  have less : event.body.depth < value.depth := by
    rw [sameValue]
    change event.body.depth < event.body.depth + 1
    omega
  exact ⟨event,sameKey,sameValue,less,fun markers => publication markers event reader cutCurrent bodyCurrent
    (smaller event.body.depth less event.expression)⟩

end MicroCFTA.SourceCurrentTrackedWriterFusion
