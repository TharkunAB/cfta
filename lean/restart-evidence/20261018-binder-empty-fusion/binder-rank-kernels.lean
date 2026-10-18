import MicroCFTA.SourceCurrentBinderFusionInduction
import MicroCFTA.SourceCurrentNativeMuGrowthExecution
import MicroCFTA.SourceCurrentRetainedMuWriterAlignment

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace MicroCFTA.BinderRankKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentRetainedMuWriterAlignment (Writer)
open InternedBinderProtocol (Reference)

private def nested : Syntax Nat Bool :=
  .binder true (.node [.mk 7 true [], .mk 9 false [.var 0]])

private def nestedUsed : Bool :=
  match build nested [] (empty (Symbol := Nat) (Guard := Bool)) with
  | .done (.mu _ _ depth ordinary) _ => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary
  | _ => false

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def expressions : List (EdgeSyntax Nat Bool) :=
  [.mk 8 false [.var 0,nested],.mk 2 true []]
private def expression : Syntax Nat Bool := .node expressions
private def requester : Syntax Nat Bool :=
  .node [.mk 2 true [],.mk 8 false [.var 0,nested],.mk 8 false [.var 0,nested]]
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
private theorem actual : build source [] empty = .done event.result reader := event.build_done
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source event.result reader actual
private theorem selected : reader.nodeRecords event.key = some event.candidate := by cbv

private theorem written :
    SourceCurrentNativeMuGrowthWriters.Written empty reader event.key event.candidate := by
  obtain ⟨path⟩ := SourceCurrentNativeMuGrowthExecution.build_path source [] empty
    SourceCurrentConstrainedCapSourceHistory.empty_context
  have actualPath : SourceCurrentNativeMuGrowthHistory.Path empty reader := by
    simpa only [actual, Outcome.state] using path
  exact SourceCurrentNativeMuGrowthWriters.from_empty actualPath event.key event.entry event.body
    event.depth event.ordinary selected

private theorem checked :
    build source [] empty = .done event.result reader ∧ Ready reader ∧
    build (.binder true requester) [] reader = .done event.result reader ∧
    requester ≠ event.expression ∧
    InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
    nestedUsed = true ∧
    SourceCurrentNativeMuGrowthWriters.Written empty reader event.key event.candidate ∧
    (∃ rawOrdinary ordinaryHeap rawBody bodyHeap,
      build event.expression (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
        event.afterDepth = .done rawOrdinary ordinaryHeap ∧
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done rawBody bodyHeap ∧
      rawOrdinary.depth = rawBody.depth ∧
      rawOrdinary.depth < event.candidate.depth ∧ rawBody.depth < event.candidate.depth) ∧
    (∃ chosen : Publication (Symbol := Nat) (Guard := Bool),
      event.key = chosen.key ∧ event.candidate = chosen.candidate ∧
      ∃ rawOrdinary ordinaryHeap rawBody bodyHeap,
        build chosen.expression (.reference (.uninterned (ordinaryLevel chosen.depth)) :: chosen.environment)
          chosen.afterDepth = .done rawOrdinary ordinaryHeap ∧
        build chosen.expression (.reference (.interned chosen.entry.identity) :: chosen.environment)
          chosen.allocated = .done rawBody bodyHeap ∧
        Grows ordinaryHeap reader ∧ Grows bodyHeap reader ∧
        rawOrdinary.depth < event.candidate.depth ∧ rawBody.depth < event.candidate.depth) := by
  refine ⟨actual, ready, ?_, ?_, ?_, ?_, written, ?_, ?_⟩
  · cbv
  · change requester ≠ expression
    simp [requester, expression, expressions]
  · cbv
  · cbv
  · obtain ⟨rawOrdinary, ordinaryHeap, rawBody, bodyHeap, ordinaryBuild, _, bodyBuild, _, _, _, _, _,
      ordinaryDepth, bodyDepth, sameDepth, _, ordinaryLess, bodyLess⟩ :=
      SourceCurrentBinderFusionInduction.publication event
    exact ⟨rawOrdinary, ordinaryHeap, rawBody, bodyHeap, ordinaryBuild, bodyBuild,
      ordinaryDepth.trans (sameDepth.trans bodyDepth.symm), ordinaryLess, bodyLess⟩
  · obtain ⟨chosen, sameKey, sameValue, rawOrdinary, ordinaryHeap, rawBody, bodyHeap, ordinaryBuild,
      _, bodyBuild, _, _, _, ordinaryGrowth, bodyGrowth, _, _, _, _, ordinaryLess, bodyLess⟩ :=
      SourceCurrentBinderFusionInduction.writer written
    exact ⟨chosen, sameKey, sameValue, rawOrdinary, ordinaryHeap, rawBody, bodyHeap, ordinaryBuild,
      bodyBuild, ordinaryGrowth, bodyGrowth, ordinaryLess, bodyLess⟩

/-- An actual earlier writer with a nested used binder supplies both strict raw callback bounds. -/
theorem earlier_writer :
    build source [] empty = .done event.result reader ∧ Ready reader ∧
    build (.binder true requester) [] reader = .done event.result reader ∧
    requester ≠ event.expression ∧
    InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
    nestedUsed = true ∧
    SourceCurrentNativeMuGrowthWriters.Written empty reader event.key event.candidate ∧
    (∃ rawOrdinary ordinaryHeap rawBody bodyHeap,
      build event.expression (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
        event.afterDepth = .done rawOrdinary ordinaryHeap ∧
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done rawBody bodyHeap ∧
      rawOrdinary.depth = rawBody.depth ∧
      rawOrdinary.depth < event.candidate.depth ∧ rawBody.depth < event.candidate.depth) ∧
    (∃ chosen : Publication (Symbol := Nat) (Guard := Bool),
      event.key = chosen.key ∧ event.candidate = chosen.candidate ∧
      ∃ rawOrdinary ordinaryHeap rawBody bodyHeap,
        build chosen.expression (.reference (.uninterned (ordinaryLevel chosen.depth)) :: chosen.environment)
          chosen.afterDepth = .done rawOrdinary ordinaryHeap ∧
        build chosen.expression (.reference (.interned chosen.entry.identity) :: chosen.environment)
          chosen.allocated = .done rawBody bodyHeap ∧
        Grows ordinaryHeap reader ∧ Grows bodyHeap reader ∧
        rawOrdinary.depth < event.candidate.depth ∧ rawBody.depth < event.candidate.depth) := checked

end MicroCFTA.BinderRankKernels
