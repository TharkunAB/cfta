import MicroCFTA.SourceCurrentUsedBinderOutputTags
import MicroCFTA.SourceEqualityRequiredCache

set_option linter.all true
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace MicroCFTA.UsedOutputKernels
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome request finish)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryLiveInputs (liftInput)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentUsedBinderAliasTransport (Aliases NamePair)
open SourceEqualityRequiredCache (Ready)
open InternedBinderProtocol (Reference)

private def output (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def expression : Syntax Nat Bool :=
  .union [.node [.mk 8 false [.var 0,.binder false (.node [.mk 9 true [.var 0,.var 1]])]],.var 0]
private def source : Syntax Nat Bool := .binder false expression
private def depthCall := callback expression [] .depth (empty (Symbol := Nat) (Guard := Bool))
private def ordinaryCall := callback expression [] (.uninterned (ordinaryLevel (output depthCall))) depthCall.state
private def key := muKey (output depthCall) (output ordinaryCall)
private def reserved := Cache.intern ordinaryCall.state.nodes key
private def allocated := {ordinaryCall.state with nodes := reserved.2}
private def bodyCall := callback expression [] (.interned reserved.1.identity) allocated
private def event : Publication (Symbol := Nat) (Guard := Bool) where
  smart := false
  expression := expression
  environment := []
  before := empty
  afterDepth := depthCall.state
  cut := ordinaryCall.state
  afterBody := bodyCall.state
  depth := output depthCall
  ordinary := output ordinaryCall
  body := output bodyCall
  context := SourceCurrentConstrainedCapSourceHistory.empty_context
  depthDone := by cbv
  ordinaryDone := by cbv
  missing := by cbv
  bodyDone := by cbv
private def reader := event.after
private theorem actual : build source [] empty = .done event.result reader := event.build_done
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source event.result reader actual
private noncomputable def history : History empty reader := by
  simpa only [actual, Outcome.state] using SourceCurrentNativeMuPublication.closed_history source
private theorem selected : reader.nodeRecords event.key = some event.candidate := by cbv
private def ignored : Reference → State Nat Bool → Outcome Nat Bool (Value Nat Bool) :=
  fun _ state => .done .empty state
private def InputAliases (writer : Publication (Symbol := Nat) (Guard := Bool)) : Prop :=
  Aliases writer.expression
    (.inr (.inl ()) :: (writer.environment.map (fun value => (Sum.inl value : Sum (Value Nat Bool) Unit))).map liftInput)
    (Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel writer.depth)) (fun _ : Unit => .depth))
    (Sum.elim (fun _ : Unit => .interned writer.entry.identity) (fun _ : Unit => .depth))
private def Names (writer : Publication (Symbol := Nat) (Guard := Bool)) : Prop :=
  (∀ name ∈ writer.ordinary.free, ∃ other ∈ writer.body.free,
    NamePair (.uninterned (ordinaryLevel writer.depth)) (.interned writer.entry.identity) name other) ∧
  (∀ other ∈ writer.body.free, ∃ name ∈ writer.ordinary.free,
    NamePair (.uninterned (ordinaryLevel writer.depth)) (.interned writer.entry.identity) name other)
private def Retained : Prop :=
  ∃ writer : Publication (Symbol := Nat) (Guard := Bool),
    event.key = writer.key ∧ event.candidate = writer.candidate ∧
    writer.afterBody.nodeRecords writer.key = none ∧
    Nonempty (History empty writer.before) ∧
    Nonempty (History writer.before writer.afterDepth) ∧
    Nonempty (History writer.afterDepth writer.cut) ∧
    Nonempty (History writer.allocated writer.afterBody) ∧ InputAliases writer ∧ Names writer
private theorem retained : Retained := by
  obtain ⟨writer,sameKey,sameValue,missing,before,first,second,third,aliases,names⟩ :=
    SourceCurrentUsedBinderAliasTransport.retained reader history event.key event.entry event.body event.depth event.ordinary selected
  have values : event.entry = writer.entry ∧ event.body = writer.body ∧
      event.depth = writer.depth ∧ event.ordinary = writer.ordinary := by
    simpa only [Publication.candidate, Value.mu.injEq] using sameValue
  refine ⟨writer,sameKey,sameValue,missing,before,first,second,third,aliases,?_⟩
  simpa only [Names,← values.1,← values.2.1,← values.2.2.1,← values.2.2.2] using names

private theorem nested_proof :
    build source [] empty = .done event.result reader ∧ Ready reader ∧ Nonempty (History empty reader) ∧
    InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
    ¬ InternedStoredShallowCompletion.BinderFree event.expression ∧
    .uninterned (ordinaryLevel event.depth) ∈ event.ordinary.free ∧
    .interned event.entry.identity ∈ event.body.free ∧ InputAliases event ∧ Names event ∧ Retained ∧
    request true event.depth event.ordinary ignored reader = .done (finish true event.candidate) reader := by
  refine ⟨actual,ready,⟨history⟩,?_,?_,?_,?_,SourceCurrentUsedBinderAliasTransport.publication event,
    SourceCurrentUsedBinderAliasTransport.publication_filtered event,retained,?_⟩
  · cbv
  · cbv
  · cbv; exact List.mem_cons_self
  · cbv; exact List.mem_cons_self
  · exact (SourceCurrentNativeMuPublication.warm history ready.semantic.1.normal.facts.coherent true
      event.depth event.ordinary ignored event.entry event.body event.depth event.ordinary selected).2


private theorem raw_tags :
    ∃ rawFirst rawHeap rawSecond rawLater,
      build event.expression (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
        event.afterDepth = .done rawFirst rawHeap ∧
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done rawSecond rawLater ∧
      (rawFirst = .reference (.uninterned (ordinaryLevel event.depth)) ↔
        rawSecond = .reference (.interned event.entry.identity)) ∧
      (rawFirst = .empty ↔ rawSecond = .empty) := by
  let inputs : List (Sum (Value Nat Bool) Unit) := event.environment.map Sum.inl
  let names : Unit → Reference := fun _ => .depth
  let localInputs := .inr (.inl ()) :: inputs.map liftInput
  let firstNames := Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) names
  let secondNames := Sum.elim (fun _ : Unit => .interned event.entry.identity) names
  have fixed : inputs.map (InternedFreshOrdinaryLiveInputs.input names) = event.environment := by
    simp [inputs,InternedFreshOrdinaryLiveInputs.input,List.map_map,Function.comp_def]
  have instantiated (own : Reference) :
      localInputs.map (InternedFreshOrdinaryLiveInputs.input (Sum.elim (fun _ : Unit => own) names)) =
        .reference own :: event.environment := by
    rw [InternedFreshOrdinaryLiveInputs.local_inputs,fixed]
  obtain ⟨rawFirst,rawHeap,rawSecond,rawLater,firstRaw,_,secondRaw,_,_,_,firstEntry,secondEntry⟩ :=
    SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have bodyArgument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have firstContext := firstEntry.base.local (.uninterned (ordinaryLevel event.depth))
    (InternedNestedProvenance.ordinary_available _ _)
  have secondContext := secondEntry.base.local (.interned event.entry.identity) bodyArgument
  have firstInputContext : InternedFreshOrdinaryContext.Context event.afterDepth
      (localInputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)) := by
    simpa only [firstNames,instantiated] using firstContext
  have secondInputContext : InternedFreshOrdinaryContext.Context event.allocated
      (localInputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)) := by
    simpa only [secondNames,instantiated] using secondContext
  have firstActual : build event.expression (localInputs.map (InternedFreshOrdinaryLiveInputs.input firstNames))
      event.afterDepth = .done rawFirst rawHeap := by simpa only [firstNames,instantiated] using firstRaw
  have secondActual : build event.expression (localInputs.map (InternedFreshOrdinaryLiveInputs.input secondNames))
      event.allocated = .done rawSecond rawLater := by simpa only [secondNames,instantiated] using secondRaw
  have localMember : (Sum.inr (Sum.inl ()) : Sum Reference (Sum Unit Unit)) ∈
      SourceCurrentUsedBinderAliasTransport.Scope event.expression localInputs := by
    cbv
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have aliases : Aliases event.expression localInputs firstNames secondNames :=
    SourceCurrentUsedBinderAliasTransport.publication event
  exact ⟨rawFirst,rawHeap,rawSecond,rawLater,firstRaw,secondRaw,
    SourceCurrentUsedBinderOutputTags.scoped_bare event.expression localInputs firstNames secondNames
      (.inr (.inl ())) localMember aliases _ _ _ _ firstInputContext secondInputContext _ _ firstActual secondActual,
    SourceCurrentUsedBinderOutputTags.empty event.expression localInputs firstNames secondNames _ _ _ _
      firstInputContext secondInputContext _ _ firstActual secondActual⟩

/-- Actual nested used source calls retain their exact output tags and an ignored warm winner. -/
theorem nested_output_tags :
    build source [] empty = .done event.result reader ∧ Ready reader ∧
    InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
    ¬ InternedStoredShallowCompletion.BinderFree event.expression ∧ Retained ∧
    request true event.depth event.ordinary ignored reader = .done (finish true event.candidate) reader ∧
    ∃ rawFirst rawHeap rawSecond rawLater,
      build event.expression (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
        event.afterDepth = .done rawFirst rawHeap ∧
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done rawSecond rawLater ∧
      (rawFirst = .reference (.uninterned (ordinaryLevel event.depth)) ↔
        rawSecond = .reference (.interned event.entry.identity)) ∧
      (rawFirst = .empty ↔ rawSecond = .empty) := by
  exact ⟨actual,ready,nested_proof.2.2.2.1,nested_proof.2.2.2.2.1,retained,nested_proof.2.2.2.2.2.2.2.2.2.2,raw_tags⟩

private def collapse : Syntax Nat Bool := .binder true (.union [
  .binder true (.var 2), .var 1,
  .node [.mk 30 false [.empty,.binder false (.node [.mk 31 true [.var 0]])]],
  .node [.mk 32 true [.empty,.var 3]]])
private def collapseInputs : List (Sum (Value Nat Bool) Unit) :=
  [.inr (),.inl (.reference .depth),.inl event.result]
private def collapseNames : Unit → Reference := fun _ => .depth
private def collapseCall := build collapse (collapseInputs.map (InternedFreshOrdinaryLiveInputs.input collapseNames)) reader
private def collapseHeap := collapseCall.state
private theorem collapseDone : collapseCall = .done (.reference .depth) collapseHeap := by cbv
private theorem collapseInputsAvailable : InternedNestedProvenance.Values reader
    (collapseInputs.map (InternedFreshOrdinaryLiveInputs.input collapseNames)) := by
  intro value member
  simp only [collapseInputs,List.map_cons,List.map_nil,InternedFreshOrdinaryLiveInputs.input,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact InternedNestedProvenance.depth_available _
  · exact InternedNestedProvenance.depth_available _
  · exact (closed_verified source).result _ _ actual
private theorem collapseContext : InternedFreshOrdinaryContext.Context reader
    (collapseInputs.map (InternedFreshOrdinaryLiveInputs.input collapseNames)) :=
  SourceRecursiveIntersectionSemanticHeap.context reader ready.semantic _ collapseInputsAvailable
private theorem collapseWarm : build collapse (collapseInputs.map (InternedFreshOrdinaryLiveInputs.input collapseNames)) collapseHeap =
    .done (.reference .depth) collapseHeap :=
  InternedFreshOrdinaryReplay.build_replay collapse _ reader collapseHeap (.reference .depth) collapseHeap
    ready.semantic.1.normal.facts.coherent.valid collapseDone (grows_refl _)
private theorem collapseAfterContext : InternedFreshOrdinaryContext.Context collapseHeap
    (collapseInputs.map (InternedFreshOrdinaryLiveInputs.input collapseNames)) := by
  exact collapseContext.build collapse

private theorem collapse_proof :
    build source [] empty = .done event.result reader ∧ Ready reader ∧
    collapseCall = .done (.reference .depth) collapseHeap ∧
    build collapse (collapseInputs.map (InternedFreshOrdinaryLiveInputs.input collapseNames)) collapseHeap =
      .done (.reference .depth) collapseHeap ∧
    (output collapseCall = .reference .depth ↔ (.reference .depth : Value Nat Bool) = .reference .depth) := by
  have aliases : Aliases collapse collapseInputs collapseNames collapseNames := fun _ _ _ _ => Iff.rfl
  have tag := SourceCurrentUsedBinderOutputTags.depth_bare collapse collapseInputs collapseNames collapseNames aliases
    reader collapseHeap collapseHeap collapseHeap collapseContext collapseAfterContext (.reference .depth) (.reference .depth)
    collapseDone collapseWarm
  refine ⟨actual,ready,collapseDone,collapseWarm,?_⟩
  rw [collapseDone]
  exact tag

/-- Nested smart root cleanup returns a captured Depth alias while discarded rows execute used binders and the replay stays warm. -/
theorem smart_root_collapse :
    build source [] empty = .done event.result reader ∧ Ready reader ∧
    collapseCall = .done (.reference .depth) collapseHeap ∧
    build collapse (collapseInputs.map (InternedFreshOrdinaryLiveInputs.input collapseNames)) collapseHeap =
      .done (.reference .depth) collapseHeap ∧
    (output collapseCall = .reference .depth ↔ (.reference .depth : Value Nat Bool) = .reference .depth) := collapse_proof

end MicroCFTA.UsedOutputKernels
