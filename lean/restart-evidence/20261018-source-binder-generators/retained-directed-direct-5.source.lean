import MicroCFTA.SourceCurrentRetainedProbeSchedule
import MicroCFTA.SourceCurrentPublicationSharedReplacements

/-!
# Actual source generators for retained Mu reconstructions

The relation contains equality and actual filtered source reconstructions.
Recursive membership occurs only in the resolved lexical inputs. Live
alias tests remain explicit. A selected writer supplies both directions
of its actual body and ordinary reconstruction generator. Its expression
can differ from the current requester's expression. This module proves
membership, not the directional simulation laws for every generator.
-/
namespace MicroCFTA.SourceCurrentRetainedMuDirectedCase
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedFreshOrdinaryLiveInputs (input liftInput local_inputs)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuGrowthHistory (Path)
open SourceCurrentNativeMuGrowthWriters (Written)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentReaderReplacementSlots (Paired Slot)
open SourceCurrentPublicationSharedReplacements (shared)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceEqualityRequiredCache (Ready Keeps)

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

mutual
/-- Equality and actual filtered source calls generate pairs before any observation law is proved. -/
inductive Generated (reader : State Symbol Guard) : Value Symbol Guard → Value Symbol Guard → Prop where
  /-- One immutable value supplies reflexive membership. -/
  | refl (value) : Generated reader value value
  /-- Historical source calls, live aliases and paired lexical inputs supply one reconstructed pair. -/
  | filtered {Atom : Type} (expression : Syntax Symbol Guard)
      (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
      (firstOwn secondOwn : Reference) (firstMap secondMap : Environment Symbol Guard)
      (firstBefore secondBefore firstRawHeap secondRawHeap firstFilterHeap secondFilterHeap : State Symbol Guard)
      (firstRaw secondRaw firstFiltered secondFiltered left right : Value Symbol Guard)
      (ready : Ready reader)
      (firstContext : Context firstBefore (inputs.map (input firstNames)))
      (secondContext : Context secondBefore (inputs.map (input secondNames)))
      (aliases : Aliases expression inputs firstNames secondNames)
      (selfTests : ∀ label ∈ Scope expression inputs,
        Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn)
      (paired : Inputs reader firstMap secondMap
        (inputs.map (input firstNames)) (inputs.map (input secondNames)))
      (firstReplacements : Replacements reader firstMap) (secondReplacements : Replacements reader secondMap)
      (firstAvailable : Available reader firstFiltered) (secondAvailable : Available reader secondFiltered)
      (firstBuild : build expression (inputs.map (input firstNames)) firstBefore = .done firstRaw firstRawHeap)
      (secondBuild : build expression (inputs.map (input secondNames)) secondBefore = .done secondRaw secondRawHeap)
      (firstFilter : run (withoutSelfReference firstOwn firstRaw) firstRawHeap = (firstFiltered,firstFilterHeap))
      (secondFilter : run (withoutSelfReference secondOwn secondRaw) secondRawHeap = (secondFiltered,secondFilterHeap))
      (firstGrowth : Grows firstRawHeap reader) (secondGrowth : Grows secondRawHeap reader)
      (firstFilteredGrowth : Grows firstFilterHeap reader) (secondFilteredGrowth : Grows secondFilterHeap reader)
      (firstWarmBuild : build expression (inputs.map (input firstNames)) reader = .done firstRaw reader)
      (secondWarmBuild : build expression (inputs.map (input secondNames)) reader = .done secondRaw reader)
      (firstWarmFilter : run (withoutSelfReference firstOwn firstRaw) reader = (firstFiltered,reader))
      (secondWarmFilter : run (withoutSelfReference secondOwn secondRaw) reader = (secondFiltered,reader))
      (firstDone : execute firstFiltered firstMap reader = .done left reader)
      (secondDone : execute secondFiltered secondMap reader = .done right reader) :
      Generated reader left right


/-- A lexical spine recurses only at resolved reference slots. Other captures retain their bindings. -/
inductive Inputs (reader : State Symbol Guard) :
    Environment Symbol Guard → Environment Symbol Guard → List (Value Symbol Guard) → List (Value Symbol Guard) → Prop where
  /-- Empty lexical lists retain both maps. -/
  | nil (first second) : Inputs reader first second [] []
  /-- A reference slot uses a previously generated pair of resolved values. -/
  | reference {first second a b left right}
      (head : Generated reader ((first a).getD (.reference a)) ((second b).getD (.reference b)))
      (tail : Inputs reader first second left right) :
      Inputs reader first second (.reference a :: left) (.reference b :: right)
  /-- An identical capture retains equal maps on each free name. -/
  | fixed {first second left right} (value : Value Symbol Guard)
      (agree : ∀ name ∈ value.free, first name = second name)
      (tail : Inputs reader first second left right) :
      Inputs reader first second (value :: left) (value :: right)
end

private theorem inputs_of_paired (reader : State Symbol Guard)
    (first second : Environment Symbol Guard) (left right : List (Value Symbol Guard))
    (paired : Paired (Generated reader) first second left right) : Inputs reader first second left right := by
  induction paired with
  | nil => exact .nil first second
  | @cons left right lefts rights head tail ih =>
      cases left <;> cases right
      all_goals try {cases head}
      case reference.reference a b => exact .reference head ih
      all_goals
        obtain ⟨same,agree⟩ := head
        cases same
        all_goals exact .fixed _ agree ih

private theorem same_inputs (event : Publication (Symbol := Symbol) (Guard := Guard))
    (own : Reference) :
    (.inr (.inl ()) :: (event.environment.map (fun value => (Sum.inl value : Sum (Value Symbol Guard) Unit))).map liftInput).map
      (input (Sum.elim (fun _ : Unit => own) (fun _ : Unit => .depth))) = .reference own :: event.environment := by
  rw [local_inputs]
  simp [input,List.map_map,Function.comp_def]

private theorem replacements (reader : State Symbol Guard)
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (value : Value Symbol Guard) (available : Available reader value) :
    Replacements reader (shared event value value (fun _ => none)) := by
  intro name output found
  dsimp only [shared,SourceCurrentStoredMuBinderChildLineage.bind] at found
  split at found
  · cases found; exact available
  · split at found
    · cases found; exact available
    · cases found

private theorem paired_reverse (reader : State Symbol Guard)
    (event : Publication (Symbol := Symbol) (Guard := Guard)) (value : Value Symbol Guard) :
    Paired (Generated reader) (shared event value value (fun _ => none)) (shared event value value (fun _ => none))
      (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
      (.reference (.interned event.entry.identity) :: event.environment) := by
  have original := SourceCurrentPublicationSharedReplacements.paired event (Generated reader)
    (Generated.refl (reader := reader)) value value (fun _ => none) (Generated.refl (reader := reader) value)
  cases original with
  | cons head tail =>
      refine .cons ?_ tail
      simpa only [Slot,shared,SourceCurrentStoredMuBinderChildLineage.bind,ite_true,
        reduceCtorEq,ite_false,Option.getD_some] using Generated.refl (reader := reader) value


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

private theorem publication_generated (event : Publication (Symbol := Symbol) (Guard := Guard))
    (reader : State Symbol Guard) (ready : Ready reader) (growth : Grows event.after reader)
    (available : Available reader event.candidate) (left right : Value Symbol Guard)
    (firstDone : execute event.body (bind (.interned event.entry.identity) event.candidate (fun _ => none)) reader = .done left reader)
    (secondDone : execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) event.candidate (fun _ => none)) reader = .done right reader) :
    Generated reader left right ∧ Generated reader right left := by
  let localInputs := .inr (.inl ()) ::
    (event.environment.map (fun value => (Sum.inl value : Sum (Value Symbol Guard) Unit))).map liftInput
  let firstNames : Sum Unit Unit → Reference := Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) (fun _ : Unit => .depth)
  let secondNames : Sum Unit Unit → Reference := Sum.elim (fun _ : Unit => .interned event.entry.identity) (fun _ : Unit => .depth)
  let maps := shared event event.candidate event.candidate (fun _ => none)
  obtain ⟨rawOrdinary,ordinaryHeap,rawBody,bodyHeap,ordinaryBuild,ordinaryFilter,bodyBuild,bodyFilter,
    ordinaryGrowth,bodyGrowth,ordinaryEntry,bodyEntry⟩ := SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  have contexts := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have bodyArgument := (InternedConstructionProvenance.reserve_available event.key event.cut
    contexts.2.1.base.normal.facts.coherent contexts.2.1.base.normal.facts.cached).2
  have ordinaryContext := ordinaryEntry.local (.uninterned (ordinaryLevel event.depth))
    (InternedNestedProvenance.ordinary_available _ _)
  have bodyContext := bodyEntry.local (.interned event.entry.identity) bodyArgument
  have bodyChecked := callback_verified event.expression event.environment (.interned event.entry.identity)
    event.allocated bodyEntry.base.normal.facts bodyContext.base.inputs
  have bodyReturned : callback event.expression event.environment (.interned event.entry.identity) event.allocated =
      .done event.body event.afterBody := event.bodyDone
  have bodyAdvance : Grows event.allocated event.afterBody := by
    simpa only [bodyReturned,Outcome.state] using bodyChecked.growth
  have afterBodyGrowth := grows_trans (SourceCurrentNativeMuGrowthHistory.publication_growth event) growth
  have cutGrowth := grows_trans (SourceCurrentNativeMuGrowthHistory.reserve_growth event)
    (grows_trans bodyAdvance afterBodyGrowth)
  have ordinaryGrowth := grows_trans ordinaryGrowth afterBodyGrowth
  have bodyGrowth := grows_trans bodyGrowth afterBodyGrowth
  have ordinaryChecked := build_verified event.expression _ event.afterDepth ordinaryContext.base.normal.facts ordinaryContext.base.inputs
  have rawBodyChecked := build_verified event.expression _ event.allocated bodyContext.base.normal.facts bodyContext.base.inputs
  have ordinaryFacts : InternedNestedFacts.Facts ordinaryHeap := by simpa only [ordinaryBuild,Outcome.state] using ordinaryChecked.facts
  have bodyFacts : InternedNestedFacts.Facts bodyHeap := by simpa only [bodyBuild,Outcome.state] using rawBodyChecked.facts
  have ordinaryWarm := InternedFreshOrdinaryReplay.build_replay event.expression _ event.afterDepth reader rawOrdinary ordinaryHeap
    ordinaryContext.base.normal.facts.coherent.valid ordinaryBuild ordinaryGrowth
  have bodyWarm := InternedFreshOrdinaryReplay.build_replay event.expression _ event.allocated reader rawBody bodyHeap
    bodyContext.base.normal.facts.coherent.valid bodyBuild bodyGrowth
  have ordinaryFilterWarm : run (withoutSelfReference (.uninterned (ordinaryLevel event.depth)) rawOrdinary) reader =
      (event.ordinary,reader) := by
    simpa only [ordinaryFilter] using InternedConstructorTemplates.replay
      (withoutSelfReference (.uninterned (ordinaryLevel event.depth)) rawOrdinary) ordinaryHeap reader
      ordinaryFacts.coherent.valid (by simpa only [ordinaryFilter] using cutGrowth)
  have bodyFilterWarm : run (withoutSelfReference (.interned event.entry.identity) rawBody) reader = (event.body,reader) := by
    simpa only [bodyFilter] using InternedConstructorTemplates.replay
      (withoutSelfReference (.interned event.entry.identity) rawBody) bodyHeap reader
      bodyFacts.coherent.valid (by simpa only [bodyFilter] using afterBodyGrowth)
  have bodyAvailable := available.children event.body (by simp [Publication.candidate,children])
  have ordinaryAvailable := available.children event.ordinary (by simp [Publication.candidate,children])
  have substitutions := SourceCurrentPublicationSharedReplacements.substitutions event event.candidate event.candidate
    (fun _ => none) reader ready.semantic.1.normal.facts.coherent bodyAvailable ordinaryAvailable
  have firstShared : execute event.body maps reader = .done left reader := substitutions.1.symm.trans firstDone
  have secondShared : execute event.ordinary maps reader = .done right reader := substitutions.2.symm.trans secondDone
  have mapAvailable : Replacements reader maps := replacements reader event event.candidate available
  have paired := SourceCurrentPublicationSharedReplacements.paired event (Generated reader)
    (Generated.refl (reader := reader)) event.candidate event.candidate (fun _ => none) (Generated.refl (reader := reader) event.candidate)
  have reverse := paired_reverse reader event event.candidate
  have aliases := SourceCurrentUsedBinderAliasTransport.publication event
  have tests := publication_tests event
  have ordinaryFirst : Generated reader right left := by
    apply Generated.filtered event.expression localInputs firstNames secondNames
      (.uninterned (ordinaryLevel event.depth)) (.interned event.entry.identity) maps maps
      event.afterDepth event.allocated ordinaryHeap bodyHeap event.cut event.afterBody
      rawOrdinary rawBody event.ordinary event.body right left ready
      (by simpa only [localInputs,firstNames,same_inputs] using ordinaryContext)
      (by simpa only [localInputs,secondNames,same_inputs] using bodyContext)
      aliases tests (by simpa only [localInputs,firstNames,secondNames,same_inputs] using
        inputs_of_paired reader maps maps _ _ reverse)
      mapAvailable mapAvailable ordinaryAvailable bodyAvailable
      (by simpa only [localInputs,firstNames,same_inputs] using ordinaryBuild)
      (by simpa only [localInputs,secondNames,same_inputs] using bodyBuild)
      ordinaryFilter bodyFilter ordinaryGrowth bodyGrowth cutGrowth afterBodyGrowth
      (by simpa only [localInputs,firstNames,same_inputs] using ordinaryWarm)
      (by simpa only [localInputs,secondNames,same_inputs] using bodyWarm)
      ordinaryFilterWarm bodyFilterWarm secondShared firstShared
  have bodyFirst : Generated reader left right := by
    apply Generated.filtered event.expression localInputs secondNames firstNames
      (.interned event.entry.identity) (.uninterned (ordinaryLevel event.depth)) maps maps
      event.allocated event.afterDepth bodyHeap ordinaryHeap event.afterBody event.cut
      rawBody rawOrdinary event.body event.ordinary left right ready
      (by simpa only [localInputs,secondNames,same_inputs] using bodyContext)
      (by simpa only [localInputs,firstNames,same_inputs] using ordinaryContext)
      (fun a ha b hb => (aliases a ha b hb).symm) (fun label member => (tests label member).symm)
      (by simpa only [localInputs,firstNames,secondNames,same_inputs] using
        inputs_of_paired reader maps maps _ _ paired)
      mapAvailable mapAvailable bodyAvailable ordinaryAvailable
      (by simpa only [localInputs,secondNames,same_inputs] using bodyBuild)
      (by simpa only [localInputs,firstNames,same_inputs] using ordinaryBuild)
      bodyFilter ordinaryFilter bodyGrowth ordinaryGrowth afterBodyGrowth cutGrowth
      (by simpa only [localInputs,secondNames,same_inputs] using bodyWarm)
      (by simpa only [localInputs,firstNames,same_inputs] using ordinaryWarm)
      bodyFilterWarm ordinaryFilterWarm firstShared secondShared
  exact ⟨bodyFirst,ordinaryFirst⟩

/-- Actual binder execution recovers its selected writer and derives both reconstructed source generators. -/
theorem binder (smart : Bool) (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard)
    (context : Context before environment)
    (actual : build (.binder smart expression) environment before = .done result after)
    (reader : State Symbol Guard) (current : Keeps after reader) (history : Path empty reader) :
    ∃ depth ordinary entry body, ∃ event : Publication (Symbol := Symbol) (Guard := Guard), ∃ left middle right final,
      reader.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      result = InternedNestedConstruction.finish smart (.mu entry body depth ordinary) ∧
      Written empty reader (muKey depth ordinary) (.mu entry body depth ordinary) ∧
      event.key = muKey depth ordinary ∧ event.candidate = .mu entry body depth ordinary ∧
      event.afterBody.nodeRecords event.key = none ∧
      Nonempty (Path empty event.before) ∧ Nonempty (Path event.before event.afterDepth) ∧
      Nonempty (Path event.afterDepth event.cut) ∧ Nonempty (Path event.allocated event.afterBody) ∧
      Grows event.after final ∧
      unfold (.mu entry body depth ordinary) reader = .done left middle ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) (.mu entry body depth ordinary) (fun _ => none))
        middle = .done right final ∧
      unfold (.mu entry body depth ordinary) final = .done left final ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) (.mu entry body depth ordinary) (fun _ => none))
        final = .done right final ∧
      left ∈ MergedFreshOrdinaryGraph.successors reader (.mu entry body depth ordinary) ∧
      left ∈ MergedFreshOrdinaryGraph.successors final (.mu entry body depth ordinary) ∧
      Keeps reader middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Generated final left right ∧ Generated final right left := by
  obtain ⟨depth,afterDepth,ordinary,cut,raw,rawHeap,entry,body,event,depthDone,ordinaryDone,requested,rawDone,filtered,
    depthContext,cutContext,rawContext,readerContext,initialGrowth,initialIssued,rawGrowth,rawIssued,
    selected,available,returned,keySame,valueSame,sameEntry,sameBody,sameDepth,sameOrdinary,
    missing,writerPrefix,depthPath,ordinaryPath,bodyPath,writerGrowth,
    left,middle,right,final,firstDone,secondDone,firstWarm,secondWarm,epsilon,firstKept,secondKept,
    leftAvailable,rightAvailable,firstHistory,secondHistory,retained⟩ :=
    SourceCurrentRetainedProbeSchedule.binder smart expression environment before result after context actual reader current history
  have finalKept := firstKept.trans secondKept
  have eventGrowth := grows_trans writerGrowth finalKept.growth
  have eventAvailable : Available final event.candidate := valueSame ▸ finalKept.available _ available
  have bodyWarm : execute event.body
      (bind (.interned event.entry.identity) event.candidate (fun _ => none)) final = .done left final := by
    rw [sameEntry,sameBody,←valueSame]
    exact firstWarm
  have ordinaryWarm : execute event.ordinary
      (bind (.uninterned (ordinaryLevel event.depth)) event.candidate (fun _ => none)) final = .done right final := by
    rw [sameDepth,sameOrdinary,←valueSame]
    exact secondWarm
  have generated := publication_generated event final finalKept.ready eventGrowth eventAvailable left right bodyWarm ordinaryWarm
  have written : Written empty reader (muKey depth ordinary) (.mu entry body depth ordinary) :=
    ⟨event,keySame,valueSame,missing,writerPrefix,depthPath,ordinaryPath,bodyPath,writerGrowth⟩
  have finalEpsilon : left ∈ MergedFreshOrdinaryGraph.successors final (.mu entry body depth ordinary) := by
    simp only [MergedFreshOrdinaryGraph.successors,firstWarm,List.mem_singleton]
  exact ⟨depth,ordinary,entry,body,event,left,middle,right,final,selected,returned,written,
    keySame.symm,valueSame.symm,missing,writerPrefix,depthPath,ordinaryPath,bodyPath,eventGrowth,firstDone,secondDone,firstWarm,secondWarm,epsilon,finalEpsilon,
    firstKept,secondKept,leftAvailable,rightAvailable,generated⟩

end MicroCFTA.SourceCurrentRetainedMuDirectedCase
