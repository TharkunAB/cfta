import MicroCFTA.SourceCurrentUsedBinderAliasTransport
import MicroCFTA.SourceEqualityRequiredCache

set_option linter.all true
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace MicroCFTA.UsedSourceAliasKernels
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

/-- A closed source with nested used recursion supplies actual filtered names and its retained warm winner. -/
theorem nested :
    build source [] empty = .done event.result reader ∧ Ready reader ∧ Nonempty (History empty reader) ∧
    InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
    ¬ InternedStoredShallowCompletion.BinderFree event.expression ∧
    .uninterned (ordinaryLevel event.depth) ∈ event.ordinary.free ∧
    .interned event.entry.identity ∈ event.body.free ∧ InputAliases event ∧ Names event ∧ Retained ∧
    request true event.depth event.ordinary ignored reader = .done (finish true event.candidate) reader := nested_proof

private def depthExpression : Syntax Nat Bool := .node [.mk 5 false [.var 0,.var 1,.var 2]]
private def depthEnvironment : List (Value Nat Bool) := [.reference .depth,.reference .depth]
private def depthSource : Syntax Nat Bool := .binder false (.binder false (.binder false depthExpression))
private def depthBuilt := build depthSource [] (empty (Symbol := Nat) (Guard := Bool))
private def firstProbe := callback depthExpression depthEnvironment .depth (empty (Symbol := Nat) (Guard := Bool))
private def secondProbe := callback depthExpression depthEnvironment
  (.uninterned (ordinaryLevel (output firstProbe))) firstProbe.state
private def depthKey := muKey (output firstProbe) (output secondProbe)
private def depthReserved := Cache.intern secondProbe.state.nodes depthKey
private def depthBody := callback depthExpression depthEnvironment (.interned depthReserved.1.identity)
  {secondProbe.state with nodes := depthReserved.2}
private def depthEvent : Publication (Symbol := Nat) (Guard := Bool) where
  smart := false
  expression := depthExpression
  environment := depthEnvironment
  before := empty
  afterDepth := firstProbe.state
  cut := secondProbe.state
  afterBody := depthBody.state
  depth := output firstProbe
  ordinary := output secondProbe
  body := output depthBody
  context := (SourceCurrentConstrainedCapSourceHistory.empty_context.local .depth
    (InternedNestedProvenance.depth_available _)).local .depth (InternedNestedProvenance.depth_available _)
  depthDone := by cbv
  ordinaryDone := by cbv
  missing := by cbv
  bodyDone := by cbv
private theorem depthActual : build depthSource [] empty = .done (output depthBuilt) depthBuilt.state := by cbv
private theorem depth_proof :
    build depthSource [] empty = .done (output depthBuilt) depthBuilt.state ∧ Ready depthBuilt.state ∧
    depthBuilt.state.nodeRecords depthEvent.key = some depthEvent.candidate ∧
    depthEvent.environment = [.reference .depth,.reference .depth] ∧
    InputAliases depthEvent ∧ Names depthEvent ∧
    .depth ∈ depthEvent.ordinary.free ∧ .depth ∈ depthEvent.body.free := by
  exact ⟨depthActual,SourceEqualityRequiredCache.constructed depthSource _ _ depthActual,by cbv,rfl,
    SourceCurrentUsedBinderAliasTransport.publication depthEvent,
    SourceCurrentUsedBinderAliasTransport.publication_filtered depthEvent,
    by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self,
    by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self⟩

/-- A reached closed construction preserves two captured Depth aliases beside its fresh local pair. -/
theorem depth_captures :
    build depthSource [] empty = .done (output depthBuilt) depthBuilt.state ∧ Ready depthBuilt.state ∧
    depthBuilt.state.nodeRecords depthEvent.key = some depthEvent.candidate ∧
    depthEvent.environment = [.reference .depth,.reference .depth] ∧
    InputAliases depthEvent ∧ Names depthEvent ∧
    .depth ∈ depthEvent.ordinary.free ∧ .depth ∈ depthEvent.body.free := depth_proof

end MicroCFTA.UsedSourceAliasKernels
