import MicroCFTA.SourceCurrentRetainedMuFiniteUnfoldEquation
import MicroCFTA.SourceCurrentOpenObservationLanguage
import MicroCFTA.SourceCurrentPublicationFiniteRootReconstruction
import MicroCFTA.SourceCurrentFiniteRootSourceNode
import MicroCFTA.SourceCurrentFiniteRootReconstruction
import MicroCFTA.SourceCurrentReaderFiniteOrdinaryStep
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.SourceCurrentStoredUnionObservations
import MicroCFTA.SourceCurrentRetainedMuWriterAlignment
import MicroCFTA.SourceCurrentWriterFiniteNodeAlignment

set_option linter.all true
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace MicroCFTA.RetainedMuEquationReview
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentRetainedMuWriterAlignment (Writer)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt AlignedAt)
open InternedBinderProtocol (Reference)
open InternedStoredSubstitution (Environment Replacements leaves encode)
open InternedStoredMuOrigins (Normal)
open InternedNestedProvenance (Values)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceCurrentPublicationSharedReplacements (shared)
open SourceCurrentLiteralRootParts (Literal)

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

private theorem children (depth : Nat) (view current : State Nat Bool)
    (rowIndex : Nat) (symbol : Nat) (guard : Bool) (originals : List (Syntax Nat Bool))
    (found : expressions[rowIndex]? = some (.mk symbol guard originals))
    (childIndex : Nat) (child : Syntax Nat Bool) (childFound : originals[childIndex]? = some child) :
    SourceCurrentFiniteObservationExecution.AlignedAt depth view current child := by
  have rowMember := List.mem_of_getElem? found
  simp only [expressions,List.mem_cons,List.not_mem_nil,or_false] at rowMember
  rcases rowMember with same | same
  · cases same
    have childMember := List.mem_of_getElem? childFound
    simp only [List.mem_cons,List.not_mem_nil,or_false] at childMember
    rcases childMember with rfl | rfl
    · exact SourceCurrentFiniteObservationExecution.reference depth view current 0
    · exact SourceCurrentFiniteObservationExecution.closed_source nested (by cbv) depth view current
  · cases same
    cases List.mem_of_getElem? childFound

private theorem callback_history (expression : Syntax Nat Bool) (environment : List (Value Nat Bool))
    (name : Reference) (before : State Nat Bool)
    (context : SourceCurrentConstrainedCapSourceHistory.Context before environment)
    (available : Available before (.reference name)) :
    Nonempty (History before (callback expression environment name before).state) := by
  obtain ⟨history⟩ := SourceCurrentNativeMuPublication.build_history expression _ before (context.local name available)
  cases actual : build expression (.reference name :: environment) before with
  | pending key after => simpa only [callback,actual,Outcome.bind,Outcome.state] using Nonempty.intro history
  | done value after =>
      have raw : History before after := by simpa only [actual,Outcome.state] using history
      exact ⟨by simpa only [callback,actual,Outcome.bind,work,Outcome.state] using
        History.trans raw (.retain after _ (InternedStoredMuOrigins.filter_noNewMu name value after))⟩

private theorem writer : Writer reader event.key event.candidate event := by
  obtain ⟨depthContext,cutContext,bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  refine ⟨rfl,rfl,?_,⟨History.refl _⟩,?_,?_,?_,?_,?_⟩
  · cbv
  · simpa only [event.depthDone,Outcome.state] using
      callback_history event.expression event.environment .depth event.before event.context
        (InternedNestedProvenance.depth_available event.before)
  · simpa only [event.ordinaryDone,Outcome.state] using
      callback_history event.expression event.environment (.uninterned (ordinaryLevel event.depth))
        event.afterDepth depthContext (InternedNestedProvenance.ordinary_available _ _)
  · have available : Available event.allocated (.reference (.interned event.entry.identity)) :=
      (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
        cutContext.base.normal.facts.cached).2
    have done : callback event.expression event.environment (.interned event.entry.identity) event.allocated =
      .done event.body event.afterBody := event.bodyDone
    simpa only [done,Outcome.state] using callback_history event.expression event.environment
      (.interned event.entry.identity) event.allocated bodyContext available
  · exact ⟨extends_refl _,extends_refl _,extends_refl _,keepFirst_extends _ _ _⟩
  · exact extends_refl _

private theorem source_checks :
    build source [] empty = .done event.result reader ∧ Ready reader ∧
    Writer reader event.key event.candidate event ∧
    build (.binder true requester) [] reader = .done event.result reader ∧
    requester ≠ event.expression ∧
    InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
    nestedUsed = true ∧
    ¬ InternedStoredShallowCompletion.BinderFree event.expression := by
  refine ⟨actual,ready,writer,?_,?_,?_,?_,?_⟩
  · cbv
  · change requester ≠ expression
    simp [requester,expression,expressions]
  · cbv
  · cbv
  · cbv


/-- A real earlier node writer derives its finite unfolding equation from its indexed source children. -/
theorem witness :
    (build source [] empty = .done event.result reader ∧ Ready reader ∧
      Writer reader event.key event.candidate event ∧
      build (.binder true requester) [] reader = .done event.result reader ∧
      requester ≠ event.expression ∧
      InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
      nestedUsed = true ∧ ¬ InternedStoredShallowCompletion.BinderFree event.expression) ∧
    ∀ count, ∃ left middle right final,
      InternedFreshOrdinaryStoredSubstitution.unfold event.candidate reader = .done left middle ∧
      execute event.ordinary
        (bind (.uninterned (ordinaryLevel event.depth)) event.candidate (fun _ => none))
        middle = .done right final ∧
      Keeps reader middle ∧ Keeps middle final ∧
      Available final left ∧ Available final right ∧
      final.nodeRecords event.key = some event.candidate ∧
      SourceCurrentOpenObservations.Same (count+1) reader [event.candidate] [right] := by
  refine ⟨source_checks,?_⟩
  intro count
  exact SourceCurrentRetainedMuFiniteUnfoldEquation.node count reader event.key event.entry event.body event.depth
    event.ordinary event writer ready selected expressions rfl
    (fun rowIndex symbol guard originals found childIndex child childFound _ execution _ =>
      children (count+1) reader execution rowIndex symbol guard originals found childIndex child childFound)

/-- One actual stored schedule preserves the finite guarded language of this nested Mu. -/
theorem language :
    (build source [] empty = .done event.result reader ∧ Ready reader ∧
      Writer reader event.key event.candidate event ∧
      build (.binder true requester) [] reader = .done event.result reader ∧
      requester ≠ event.expression ∧
      InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
      nestedUsed = true ∧ ¬ InternedStoredShallowCompletion.BinderFree event.expression) ∧
    ∃ left middle right final,
      InternedFreshOrdinaryStoredSubstitution.unfold event.candidate reader = .done left middle ∧
      execute event.ordinary
        (bind (.uninterned (ordinaryLevel event.depth)) event.candidate (fun _ => none))
        middle = .done right final ∧
      Keeps reader middle ∧ Keeps middle final ∧
      Available final left ∧ Available final right ∧
      final.nodeRecords event.key = some event.candidate ∧
      ∀ meaning term,
        EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph reader meaning) event.candidate term ↔
        EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph reader meaning) right term := by
  obtain ⟨source, steps⟩ := witness
  obtain ⟨left,middle,right,final,actual,secondDone,firstKept,secondKept,
    leftAvailable,rightAvailable,record,_⟩ := steps 0
  refine ⟨source,left,middle,right,final,actual,secondDone,firstKept,secondKept,
    leftAvailable,rightAvailable,record,?_⟩
  intro meaning term
  obtain ⟨newLeft,newMiddle,newRight,newFinal,newActual,newSecond,_,_,_,_,_,observed⟩ := steps term.height
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (actual.symm.trans newActual)
  obtain ⟨rfl,_⟩ := Outcome.done.inj (secondDone.symm.trans newSecond)
  exact SourceCurrentOpenObservationLanguage.finite reader meaning (term.height+1)
    event.candidate right term (Nat.le_succ _) observed

end MicroCFTA.RetainedMuEquationReview
