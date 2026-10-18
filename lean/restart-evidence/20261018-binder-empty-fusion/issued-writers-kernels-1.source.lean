import MicroCFTA.SourceCurrentNativeMuIssuedWriters

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.IssuedWriterKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceEqualityRequiredCache (Ready Keeps)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def seed : Syntax Nat Bool := .node [.mk 0 true []]
private def seedCall := build seed [] empty
private def first := seedCall.state
private def unused : Value Nat Bool := .reference (.interned 0)
private def captures : List (Value Nat Bool) := [unused]
private def expression : Syntax Nat Bool := .node [.mk 7 true [.var 0]]
private def source : Syntax Nat Bool := .binder false expression
private def depthCall := callback expression captures .depth first
private def ordinaryCall := callback expression captures (.uninterned (ordinaryLevel (value depthCall))) depthCall.state
private def key := muKey (value depthCall) (value ordinaryCall)
private def reserved := Cache.intern ordinaryCall.state.nodes key
private def allocated := {ordinaryCall.state with nodes := reserved.2}
private def bodyCall := callback expression captures (.interned reserved.1.identity) allocated
private theorem seed_done : build seed [] empty = .done (value seedCall) first := by cbv
private theorem seed_ready : Ready first := SourceEqualityRequiredCache.constructed seed (value seedCall) first seed_done
private theorem unused_available : Available first unused := by
  apply reference_available first (.interned 0)
  intro identity member
  have same : identity = 0 := by simpa only [Value.free,List.mem_singleton,Reference.interned.injEq] using member
  subst identity
  exact ⟨(first.nodes.issued 0).getD (.node []),by cbv⟩
private theorem context : Context first captures := by
  have initial : Context first [] := by
    simpa only [seed_done,Outcome.state] using SourceCurrentConstrainedCapSourceHistory.empty_context.build seed
  exact initial.local (.interned 0) unused_available
private def event : Publication (Symbol := Nat) (Guard := Bool) where
  smart := false
  expression := expression
  environment := captures
  before := first
  afterDepth := depthCall.state
  cut := ordinaryCall.state
  afterBody := bodyCall.state
  depth := value depthCall
  ordinary := value ordinaryCall
  body := value bodyCall
  context := context
  depthDone := by cbv
  ordinaryDone := by cbv
  missing := by cbv
  bodyDone := by cbv
private def reader := event.after
private theorem actual : build source captures first = .done event.result reader := event.build_done
private theorem current : Keeps first reader := by
  have available := context.base.inputs
  have checked := build_verified source captures first seed_ready.semantic.1.normal.facts available
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source source captures first seed_ready.semantic available
  · exact InternedFreshOrdinaryCoverage.build_covered source captures first seed_ready.semantic.1.normal.facts.coherent.valid
      seed_ready.covered event.result reader actual
  · simpa only [actual,Outcome.state] using (InternedOpenDepthExecution.build_depth source captures first
      (SourceRecursiveIntersectionSemanticHeap.context first seed_ready.semantic captures available) seed_ready.semantic.2 seed_ready.depth).heap
  · simpa only [actual,Outcome.state] using checked.growth
  · simpa only [actual,Outcome.state] using checked.history
private theorem actual_path : Nonempty (Path empty reader) := by
  obtain ⟨seedPath⟩ := SourceCurrentNativeMuIssuedHistory.build_path seed [] empty SourceCurrentConstrainedCapSourceHistory.empty_context
  have initial : Path empty first := by simpa only [seed_done,Outcome.state] using seedPath
  obtain ⟨writerPath⟩ := SourceCurrentNativeMuIssuedHistory.build_path source captures first context
  have final : Path first reader := by simpa only [actual,Outcome.state] using writerPath
  exact ⟨.trans initial final⟩
private theorem selected : reader.nodeRecords event.key = some event.candidate := by cbv
private theorem written : SourceCurrentNativeMuIssuedWriters.Written empty reader event.key event.candidate :=
  SourceCurrentNativeMuIssuedWriters.from_empty (Classical.choice actual_path) event.key event.entry event.body event.depth event.ordinary selected

private theorem checked :
    build source captures first = .done event.result reader ∧ Ready reader ∧
    event.environment = [unused] ∧ Available reader unused ∧
    SourceCurrentNativeMuIssuedWriters.Written empty reader event.key event.candidate ∧
    ∃ chosen : Publication (Symbol := Nat) (Guard := Bool),
      event.key = chosen.key ∧ event.candidate = chosen.candidate ∧
      ∃ rawOrdinary ordinaryHeap rawBody bodyHeap,
        build chosen.expression (.reference (.uninterned (ordinaryLevel chosen.depth)) :: chosen.environment)
          chosen.afterDepth = .done rawOrdinary ordinaryHeap ∧
        build chosen.expression (.reference (.interned chosen.entry.identity) :: chosen.environment)
          chosen.allocated = .done rawBody bodyHeap ∧
        Context reader (.reference (.uninterned (ordinaryLevel chosen.depth)) :: chosen.environment) ∧
        Context reader (.reference (.interned chosen.entry.identity) :: chosen.environment) ∧
        Keeps ordinaryHeap reader ∧ Keeps bodyHeap reader ∧
        build chosen.expression (.reference (.uninterned (ordinaryLevel chosen.depth)) :: chosen.environment)
          reader = .done rawOrdinary reader ∧
        run (withoutSelfReference (.uninterned (ordinaryLevel chosen.depth)) rawOrdinary) reader = (chosen.ordinary,reader) ∧
        build chosen.expression (.reference (.interned chosen.entry.identity) :: chosen.environment)
          reader = .done rawBody reader ∧
        run (withoutSelfReference (.interned chosen.entry.identity) rawBody) reader = (chosen.body,reader) := by
  refine ⟨actual,current.ready,rfl,current.available unused unused_available,written,?_⟩
  obtain ⟨chosen,keySame,valueSame,rawOrdinary,ordinaryHeap,rawBody,bodyHeap,ordinaryBuild,_ordinaryFilter,bodyBuild,_bodyFilter,
    ordinaryContext,bodyContext,ordinaryKeeps,bodyKeeps,_ordinaryAvailable,_bodyAvailable,ordinaryWarm,ordinaryFilterWarm,bodyWarm,bodyFilterWarm⟩ :=
    SourceCurrentNativeMuIssuedWriters.Written.raw_contexts written current.ready
  exact ⟨chosen,keySame,valueSame,rawOrdinary,ordinaryHeap,rawBody,bodyHeap,ordinaryBuild,bodyBuild,
    ordinaryContext,bodyContext,ordinaryKeeps,bodyKeeps,ordinaryWarm,ordinaryFilterWarm,bodyWarm,bodyFilterWarm⟩

/-- The recovered earlier writer derives both original contexts and adjacent raw/filter calls at the actual reader. -/
theorem selected_contexts :
    build source captures first = .done event.result reader ∧ Ready reader ∧
    event.environment = [unused] ∧ Available reader unused ∧
    SourceCurrentNativeMuIssuedWriters.Written empty reader event.key event.candidate ∧
    ∃ chosen : Publication (Symbol := Nat) (Guard := Bool),
      event.key = chosen.key ∧ event.candidate = chosen.candidate ∧
      ∃ rawOrdinary ordinaryHeap rawBody bodyHeap,
        build chosen.expression (.reference (.uninterned (ordinaryLevel chosen.depth)) :: chosen.environment)
          chosen.afterDepth = .done rawOrdinary ordinaryHeap ∧
        build chosen.expression (.reference (.interned chosen.entry.identity) :: chosen.environment)
          chosen.allocated = .done rawBody bodyHeap ∧
        Context reader (.reference (.uninterned (ordinaryLevel chosen.depth)) :: chosen.environment) ∧
        Context reader (.reference (.interned chosen.entry.identity) :: chosen.environment) ∧
        Keeps ordinaryHeap reader ∧ Keeps bodyHeap reader ∧
        build chosen.expression (.reference (.uninterned (ordinaryLevel chosen.depth)) :: chosen.environment)
          reader = .done rawOrdinary reader ∧
        run (withoutSelfReference (.uninterned (ordinaryLevel chosen.depth)) rawOrdinary) reader = (chosen.ordinary,reader) ∧
        build chosen.expression (.reference (.interned chosen.entry.identity) :: chosen.environment)
          reader = .done rawBody reader ∧
        run (withoutSelfReference (.interned chosen.entry.identity) rawBody) reader = (chosen.body,reader) := checked

end MicroCFTA.IssuedWriterKernels
