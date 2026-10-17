import MicroCFTA.SourceCurrentRetainedMuWriterAlignment
import MicroCFTA.InternedFreshOrdinaryFirstOrderHeap

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace MicroCFTA.RetainedWriterKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome request finish)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentRetainedMuWriterAlignment (Writer Reconstruction)
open InternedBinderProtocol (Reference)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def expression : Syntax Nat Bool :=
  .union [.node [.mk 8 false [.var 0],.mk 2 true []],.var 0]
private def requester : Syntax Nat Bool :=
  .union [.node [.mk 2 true [],.mk 8 false [.var 0],.mk 8 false [.var 0]],.var 0,.empty]
private def source : Syntax Nat Bool := .binder false expression
private def depthCall := callback expression [] .depth (empty (Symbol := Nat) (Guard := Bool))
private def ordinaryCall := callback expression [] (.uninterned (ordinaryLevel (value depthCall))) depthCall.state
private def key := muKey (value depthCall) (value ordinaryCall)
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
  depth := value depthCall
  ordinary := value ordinaryCall
  body := value bodyCall
  context := SourceCurrentConstrainedCapSourceHistory.empty_context
  depthDone := by cbv
  ordinaryDone := by cbv
  missing := by cbv
  bodyDone := by cbv
private def reader := event.after
private def ignored : Reference → State Nat Bool → Outcome Nat Bool (Value Nat Bool) :=
  fun _ state => .done .empty state
private theorem actual : build source [] empty = .done event.result reader := event.build_done
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source event.result reader actual
private theorem selected : reader.nodeRecords event.key = some event.candidate := by cbv
private theorem free : InternedStoredShallowCompletion.BinderFree event.expression := by cbv

private theorem writer : Writer reader event.key event.candidate event := by
  refine ⟨rfl,rfl,?_,⟨History.refl _⟩,?_,?_,?_,?_,?_⟩
  · cbv
  · have noNew := InternedFreshOrdinaryFirstOrderHeap.callback_noNewMu event.expression free event.environment .depth event.before
    exact ⟨.retain _ _ (by simpa only [event.depthDone,Outcome.state] using noNew)⟩
  · have noNew := InternedFreshOrdinaryFirstOrderHeap.callback_noNewMu event.expression free event.environment
      (.uninterned (ordinaryLevel event.depth)) event.afterDepth
    exact ⟨.retain _ _ (by simpa only [event.ordinaryDone,Outcome.state] using noNew)⟩
  · have noNew := InternedFreshOrdinaryFirstOrderHeap.callback_noNewMu event.expression free event.environment
      (.interned event.entry.identity) event.allocated
    have bodyDone : callback event.expression event.environment (.interned event.entry.identity) event.allocated =
      .done event.body event.afterBody := event.bodyDone
    exact ⟨.retain _ _ (by simpa only [bodyDone,Outcome.state] using noNew)⟩
  · exact ⟨extends_refl _,extends_refl _,extends_refl _,keepFirst_extends _ _ _⟩
  · exact extends_refl _

private theorem witness_proof :
    build source [] empty = .done event.result reader ∧
    build (.binder true requester) [] reader = .done event.result reader ∧
    requester ≠ event.expression ∧
    InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
    Writer reader event.key event.candidate event ∧
    (∃ recovered, Writer reader event.key event.candidate recovered ∧
      (InternedStoredShallowCompletion.BinderFree recovered.expression →
        ∀ replacement, Available reader replacement →
          Reconstruction event.entry event.body event.depth event.ordinary replacement reader)) ∧
    Reconstruction event.entry event.body event.depth event.ordinary event.result reader ∧
    ignored (.interned event.entry.identity) reader = .done .empty reader ∧
    event.body ≠ .empty ∧
    request true event.depth event.ordinary ignored reader = .done event.result reader := by
  have present : reader.nodeRecords event.key = some (.mu event.entry event.body event.depth event.ordinary) := selected
  obtain ⟨recovered,recoveredWriter,_,reconstruct,warm,_⟩ := SourceCurrentRetainedMuWriterAlignment.retained
    source event.result reader actual reader (SourceEqualityRequiredCache.pure_keeps reader ready)
    event.key event.entry event.body event.depth event.ordinary present
  have replacementAvailable : Available reader event.result := by
    have same : event.result = event.candidate := by cbv
    rw [same]
    exact ready.semantic.1.normal.facts.cached.nodes event.key event.candidate selected
  refine ⟨actual,?_,?_,?_,writer,⟨recovered,recoveredWriter,reconstruct⟩,
    writer.reconstruct free ready event.result replacementAvailable,rfl,?_,?_⟩
  · cbv
  · change requester ≠ expression
    simp [requester,expression]
  · cbv
  · cbv
    intro impossible
    cases impossible
  · have call := warm true ignored
    have same : finish true (.mu event.entry event.body event.depth event.ordinary) = event.result := by cbv
    rw [same] at call
    exact call

/-- A changed warm source and an ignored distinct callback retain the actual first writer and both reconstruction schedules. -/
theorem witness :
    build source [] empty = .done event.result reader ∧
    build (.binder true requester) [] reader = .done event.result reader ∧
    requester ≠ event.expression ∧
    InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
    Writer reader event.key event.candidate event ∧
    (∃ recovered, Writer reader event.key event.candidate recovered ∧
      (InternedStoredShallowCompletion.BinderFree recovered.expression →
        ∀ replacement, Available reader replacement →
          Reconstruction event.entry event.body event.depth event.ordinary replacement reader)) ∧
    Reconstruction event.entry event.body event.depth event.ordinary event.result reader ∧
    ignored (.interned event.entry.identity) reader = .done .empty reader ∧
    event.body ≠ .empty ∧
    request true event.depth event.ordinary ignored reader = .done event.result reader := witness_proof

/-- The same actual source invokes the initial producer without supplied completion or writer evidence. -/
theorem initial_producer :
    ∃ result before, build source [] empty = .done result before ∧ Ready before ∧
      ∀ key entry body depth ordinary,
        before.nodeRecords key = some (.mu entry body depth ordinary) →
        ∃ recovered, Writer before key (.mu entry body depth ordinary) recovered ∧
          before.nodeRecords key = some (.mu entry body depth ordinary) ∧
          (InternedStoredShallowCompletion.BinderFree recovered.expression →
            ∀ replacement, Available before replacement → Reconstruction entry body depth ordinary replacement before) ∧
          (∀ (smart : Bool) (next : Reference → State Nat Bool → Outcome Nat Bool (Value Nat Bool)),
            request smart depth ordinary next before = .done (finish smart (.mu entry body depth ordinary)) before) ∧
          (InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false →
            finish true (.mu entry body depth ordinary) =
              SourceCurrentNativeCallbackErasure.eraseSelf (.uninterned (ordinaryLevel depth)) ordinary) :=
  SourceCurrentRetainedMuWriterAlignment.initial source

end MicroCFTA.RetainedWriterKernels

#check @MicroCFTA.RetainedWriterKernels.witness
#print MicroCFTA.RetainedWriterKernels.witness
#print axioms MicroCFTA.RetainedWriterKernels.witness

#check @MicroCFTA.RetainedWriterKernels.initial_producer
#print MicroCFTA.RetainedWriterKernels.initial_producer
#print axioms MicroCFTA.RetainedWriterKernels.initial_producer
