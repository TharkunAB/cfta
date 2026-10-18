import MicroCFTA.SourceCurrentBoundedWriterFusion
import MicroCFTA.SourceCurrentFilteredBinderFreeFusion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.BoundedWriterKernels
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
private def capturedRef : Value Nat Bool := .reference (.interned 0)
private def captures : List (Value Nat Bool) := [capturedRef]
private def expression : Syntax Nat Bool := .node [.mk 7 true [.var 0,.var 1]]
private def source : Syntax Nat Bool := .binder false expression
private def depthCall := callback expression captures .depth first
private def ordinaryCall := callback expression captures (.uninterned (ordinaryLevel (value depthCall))) depthCall.state
private def key := muKey (value depthCall) (value ordinaryCall)
private def reserved := Cache.intern ordinaryCall.state.nodes key
private def allocated := {ordinaryCall.state with nodes := reserved.2}
private def bodyCall := callback expression captures (.interned reserved.1.identity) allocated
private theorem seed_done : build seed [] empty = .done (value seedCall) first := by cbv
private theorem seed_ready : Ready first := SourceEqualityRequiredCache.constructed seed (value seedCall) first seed_done
private theorem capturedRef_available : Available first capturedRef := by
  apply reference_available first (.interned 0)
  intro identity member
  have same : identity = 0 := by simpa only [Value.free,List.mem_singleton,Reference.interned.injEq] using member
  subst identity
  exact ⟨(first.nodes.issued 0).getD (.node []),by cbv⟩
private theorem context : Context first captures := by
  have initial : Context first [] := by
    simpa only [seed_done,Outcome.state] using SourceCurrentConstrainedCapSourceHistory.empty_context.build seed
  exact initial.local (.interned 0) capturedRef_available
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

open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceCurrentStoredMuBinderChildLineage (bind)

private theorem candidate_available : Available reader event.candidate :=
  current.ready.semantic.1.normal.facts.cached.nodes event.key event.candidate selected
private def environment : Environment Nat Bool := fun name => if name = .interned 0 then some .empty else none
private def prepare : Syntax Nat Bool := .node [.mk 7 true [.var 0,.empty]]
private def prepared := build prepare [event.candidate] reader
private def final := prepared.state
private theorem prepare_context : Context reader [event.candidate] := by
  refine ⟨SourceRecursiveIntersectionSemanticHeap.context reader current.ready.semantic _ ?_,current.ready.semantic.2⟩
  intro value member
  have same : value = event.candidate := by simpa only [List.mem_singleton] using member
  subst value
  exact candidate_available
private theorem prepare_done : build prepare [event.candidate] reader = .done .empty final := by cbv
private theorem prepared_current : Keeps reader final := by
  have checked := build_verified prepare [event.candidate] reader prepare_context.base.normal.facts prepare_context.base.inputs
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [prepare_done,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source prepare [event.candidate]
      reader current.ready.semantic prepare_context.base.inputs
  · exact InternedFreshOrdinaryCoverage.build_covered prepare [event.candidate] reader prepare_context.base.normal.facts.coherent.valid
      current.ready.covered .empty final prepare_done
  · simpa only [prepare_done,Outcome.state] using (InternedOpenDepthExecution.build_depth prepare [event.candidate]
      reader prepare_context.base current.ready.semantic.2 current.ready.depth).heap
  · simpa only [prepare_done,Outcome.state] using checked.growth
  · simpa only [prepare_done,Outcome.state] using checked.history
private theorem body_current : Keeps event.afterBody final := by
  apply Keeps.trans (middle := reader)
  · exact ⟨current.ready,SourceCurrentNativeMuGrowthHistory.publication_growth event,extends_refl _⟩
  · exact prepared_current
private theorem cut_current : Keeps event.cut final := by
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have allocatedContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.2
  have argument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have checked := callback_verified event.expression event.environment (.interned event.entry.identity) event.allocated
    allocatedContext.base.normal.facts (allocatedContext.base.local _ argument).inputs
  have growth : Grows event.allocated event.afterBody := by simpa only [event.bodyDone,Outcome.state] using checked.growth
  have issued : Extends event.allocated.nodes.issued event.afterBody.nodes.issued := by
    simpa only [event.bodyDone,Outcome.state] using checked.history
  have reserveIssued : Extends event.cut.nodes.issued event.allocated.nodes.issued :=
    InternedFreshProbeKeys.intern_issued_extends event.cut.nodes event.key cutContext.base.normal.facts.coherent.valid.2
  exact ⟨body_current.ready,grows_trans (SourceCurrentNativeMuGrowthHistory.reserve_growth event)
    (grows_trans growth body_current.growth),extends_trans reserveIssued (extends_trans issued body_current.history)⟩
private theorem replacements : Replacements final environment := by
  intro name value found
  dsimp only [environment] at found
  split at found
  · cases found; exact InternedNestedProvenance.empty_available final
  · cases found
private theorem body_done : execute event.body (bind (.interned event.entry.identity) event.candidate environment)
    final = .done .empty final := by cbv
private theorem ordinary_done : execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) event.candidate environment)
    final = .done .empty final := by cbv
private theorem smaller : SourceCurrentBoundedFilteredFusion.Fusion event.body.depth event.expression :=
  SourceCurrentBoundedFilteredFusion.of_fusion event.body.depth event.expression
    (SourceCurrentFilteredBinderFreeFusion.source event.expression (by cbv))
private theorem checked :
    build source captures first = .done event.result reader ∧ Ready final ∧
    SourceCurrentNativeMuIssuedWriters.Written empty reader event.key event.candidate ∧
    Reference.interned 0 ∈ event.body.free ∧ environment (.interned 0) = some .empty ∧
    event.candidate.referenceOf ≠ .empty ∧ Keeps event.cut final ∧ Keeps event.afterBody final ∧
    execute event.body (bind (.interned event.entry.identity) event.candidate environment) final = .done .empty final ∧
    execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) event.candidate environment) final = .done .empty final ∧
    ((Value.empty : Value Nat Bool).referenceOf == .empty) = (Value.empty.referenceOf == .empty) := by
  have available := prepared_current.available event.candidate candidate_available
  have fusion := SourceCurrentBoundedWriterFusion.publication event final cut_current body_current smaller
    event.candidate event.candidate environment available available replacements rfl .empty .empty body_done ordinary_done
  exact ⟨actual,prepared_current.ready,written,(by cbv; exact List.mem_cons_of_mem _ (List.mem_cons_self)),rfl,
    (by cbv; intro impossible; cases impossible),cut_current,body_current,body_done,ordinary_done,fusion⟩

/-- Actual used callbacks retain arbitrary outer Empty replacements under a derived bounded body law. -/
theorem captured_empty :
    build source captures first = .done event.result reader ∧ Ready final ∧
    SourceCurrentNativeMuIssuedWriters.Written empty reader event.key event.candidate ∧
    Reference.interned 0 ∈ event.body.free ∧ environment (.interned 0) = some .empty ∧
    event.candidate.referenceOf ≠ .empty ∧ Keeps event.cut final ∧ Keeps event.afterBody final ∧
    execute event.body (bind (.interned event.entry.identity) event.candidate environment) final = .done .empty final ∧
    execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) event.candidate environment) final = .done .empty final ∧
    ((Value.empty : Value Nat Bool).referenceOf == .empty) = (Value.empty.referenceOf == .empty) := checked

end MicroCFTA.BoundedWriterKernels
