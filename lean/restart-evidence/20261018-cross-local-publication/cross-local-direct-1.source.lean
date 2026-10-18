import MicroCFTA.SourceCurrentPublicationReconstructionGenerators
import MicroCFTA.SourceCurrentOpenPreorderSimulation

/-!
# Actual cross-local publication generators

One selected publication supplies both filtered source generators at one reader.
The local replacements have both Generated directions. The outer map is shared.
The proof retains the historical callback states and the exact warm replays.
It proves relation membership. It does not prove an observation law.
-/
namespace MicroCFTA.SourceCurrentPublicationCrossLocalGenerators
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedFreshOrdinaryLiveInputs (input liftInput local_inputs)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentReaderReplacementSlots (Paired Slot)
open SourceCurrentPublicationSharedReplacements (shared)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceEqualityRequiredCache (Ready Keeps)

open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceCurrentOpenPreorderSimulation (Mutual)

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

private theorem inputs_of_paired (reader : State Symbol Guard)
    (first second : Environment Symbol Guard) (left right : List (Value Symbol Guard))
    (paired : Paired (fun a b => Generated reader a b ∧ Generated reader b a) first second left right) : Inputs reader first second left right := by
  induction paired with
  | nil => exact .nil first second
  | @cons left right lefts rights head tail ih =>
      cases left <;> cases right
      all_goals try {cases head}
      case reference.reference a b => exact .reference head.1 head.2 ih
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
    (first second : Value Symbol Guard) (firstAvailable : Available reader first)
    (secondAvailable : Available reader second)
    (outer : Environment Symbol Guard) (replaced : Replacements reader outer) :
    Replacements reader (shared event first second outer) := by
  intro name output found
  dsimp only [shared,SourceCurrentStoredMuBinderChildLineage.bind] at found
  split at found
  · cases found; exact firstAvailable
  · split at found
    · cases found; exact secondAvailable
    · exact replaced name output found

private theorem paired_reverse (reader : State Symbol Guard)
    (event : Publication (Symbol := Symbol) (Guard := Guard)) (first second : Value Symbol Guard)
    (outer : Environment Symbol Guard) (related : Mutual (Generated reader) first second) :
    Paired (Mutual (Generated reader)) (shared event first second outer) (shared event first second outer)
      (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
      (.reference (.interned event.entry.identity) :: event.environment) := by
  have original := SourceCurrentPublicationSharedReplacements.paired event
    (Mutual (Generated reader))
    (fun value => ⟨Generated.refl value,Generated.refl value⟩) first second outer related
  cases original with
  | cons head tail =>
      refine .cons ?_ tail
      simpa only [Slot,shared,SourceCurrentStoredMuBinderChildLineage.bind,ite_true,
        reduceCtorEq,ite_false,Option.getD_some] using
        (show Mutual (Generated reader) second first from ⟨related.2,related.1⟩)


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

/-- Related local replacements and actual warm calls derive both publication reconstruction generators. -/
theorem publication (event : Publication (Symbol := Symbol) (Guard := Guard))
    (reader : State Symbol Guard) (ready : Ready reader) (growth : Grows event.after reader)
    (payloadAvailable : Available reader event.candidate)
    (outer : Environment Symbol Guard) (outerReplacements : Replacements reader outer)
    (firstReplacement secondReplacement : Value Symbol Guard)
    (firstAvailable : Available reader firstReplacement) (secondAvailable : Available reader secondReplacement)
    (related : Mutual (Generated reader) firstReplacement secondReplacement)
    (left right : Value Symbol Guard)
    (firstDone : execute event.body (bind (.interned event.entry.identity) firstReplacement outer) reader = .done left reader)
    (secondDone : execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) secondReplacement outer) reader = .done right reader) :
    Mutual (Generated reader) left right := by
  let localInputs := .inr (.inl ()) ::
    (event.environment.map (fun value => (Sum.inl value : Sum (Value Symbol Guard) Unit))).map liftInput
  let firstNames : Sum Unit Unit → Reference := Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) (fun _ : Unit => .depth)
  let secondNames : Sum Unit Unit → Reference := Sum.elim (fun _ : Unit => .interned event.entry.identity) (fun _ : Unit => .depth)
  let maps := shared event firstReplacement secondReplacement outer
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
  have bodyAvailable := payloadAvailable.children event.body (by simp [Publication.candidate,children])
  have ordinaryAvailable := payloadAvailable.children event.ordinary (by simp [Publication.candidate,children])
  have substitutions := SourceCurrentPublicationSharedReplacements.substitutions event firstReplacement secondReplacement
    outer reader ready.semantic.1.normal.facts.coherent bodyAvailable ordinaryAvailable
  have firstShared : execute event.body maps reader = .done left reader := substitutions.1.symm.trans firstDone
  have secondShared : execute event.ordinary maps reader = .done right reader := substitutions.2.symm.trans secondDone
  have mapAvailable : Replacements reader maps := replacements reader event firstReplacement secondReplacement firstAvailable secondAvailable outer outerReplacements
  have paired := SourceCurrentPublicationSharedReplacements.paired event
    (Mutual (Generated reader))
    (fun value => ⟨Generated.refl value,Generated.refl value⟩) firstReplacement secondReplacement outer related
  have reverse := paired_reverse reader event firstReplacement secondReplacement outer related
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

end MicroCFTA.SourceCurrentPublicationCrossLocalGenerators
