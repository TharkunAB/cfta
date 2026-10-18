import MicroCFTA.SourceCurrentReaderFiniteOrdinaryStep
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.SourceCurrentStoredUnionObservations
import MicroCFTA.SourceCurrentRetainedMuWriterAlignment
import MicroCFTA.SourceCurrentWriterFiniteNodeAlignment

set_option linter.all true
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace MicroCFTA.WriterSourceReviewKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentRetainedMuWriterAlignment (Writer)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt AlignedAt)
open InternedBinderProtocol (Reference)

private def nested : Syntax Nat Bool :=
  .binder true (.node [.mk 7 true [], .mk 9 false [.var 0]])

private def nestedUsed : Bool :=
  match build nested [] (empty (Symbol := Nat) (Guard := Bool)) with
  | .done (.mu _ _ depth ordinary) _ => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary
  | _ => false

private theorem nested_aligned (depth : Nat) (reader : State Nat Bool) :
    AlignedAt depth reader nested := by
  intro leftInputs rightInputs first second paired ready firstInputs secondInputs
    firstReplacements secondReplacements rawFirst rawSecond firstRaw secondRaw result other firstDone secondDone
  have independent (inputs : List (Value Nat Bool)) : build nested inputs reader = build nested [] reader := by
    apply InternedFreshOrdinaryDependencies.build_congr
    intro index member
    have noInputs : InternedNestedDependencies.inputs nested = [] := by cbv
    rw [noInputs] at member
    cases member
  have same : rawFirst = rawSecond :=
    (Outcome.done.inj (firstRaw.symm.trans ((independent leftInputs).trans
      ((independent rightInputs).symm.trans secondRaw)))).1
  subst rawSecond
  have closed : rawFirst.free = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name member
    have raw : build nested [] reader = .done rawFirst reader := (independent leftInputs).symm.trans firstRaw
    obtain ⟨value,impossible,_⟩ := InternedFreshOrdinarySourceFreeNames.build_free_origins nested [] reader
      ready.semantic.1.normal (by intro value impossible; cases impossible) ready.semantic.1.freeNames
      ready.semantic.1.profiles rawFirst reader raw name member
    cases impossible
  have firstClosed := SourceCurrentStoredUnionObservations.closed rawFirst first reader closed
  have secondClosed := SourceCurrentStoredUnionObservations.closed rawFirst second reader closed
  have left : result = rawFirst := (Outcome.done.inj (firstDone.symm.trans firstClosed)).1
  have right : other = rawFirst := (Outcome.done.inj (secondDone.symm.trans secondClosed)).1
  subst result
  subst other
  exact ⟨Iff.rfl,SourceCurrentOpenObservations.Same.refl depth reader [rawFirst]⟩

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

private theorem children (depth : Nat) (current : State Nat Bool)
    (rowIndex : Nat) (symbol : Nat) (guard : Bool) (originals : List (Syntax Nat Bool))
    (found : expressions[rowIndex]? = some (.mk symbol guard originals))
    (childIndex : Nat) (child : Syntax Nat Bool) (childFound : originals[childIndex]? = some child) :
    AlignedAt depth current child := by
  have rowMember := List.mem_of_getElem? found
  simp only [expressions,List.mem_cons,List.not_mem_nil,or_false] at rowMember
  rcases rowMember with same | same
  · cases same
    have childMember := List.mem_of_getElem? childFound
    simp only [List.mem_cons,List.not_mem_nil,or_false] at childMember
    rcases childMember with rfl | rfl
    · exact SourceCurrentReaderFiniteOrdinaryStep.reference depth current 0
    · exact nested_aligned depth current
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

private theorem witness_proof :
    (build source [] empty = .done event.result reader ∧ Ready reader ∧
      Writer reader event.key event.candidate event ∧
      build (.binder true requester) [] reader = .done event.result reader ∧
      requester ≠ event.expression ∧
      InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
      nestedUsed = true ∧ ¬ InternedStoredShallowCompletion.BinderFree event.expression) ∧
    ∀ depth, SourceCurrentWriterFiniteNodeAlignment.ReconstructionAt (depth + 1)
      event.entry event.body event.depth event.ordinary event.result reader := by
  refine ⟨source_checks,?_⟩
  intro depth
  have available : Available reader event.result := by
    have same : event.result = event.candidate := by cbv
    rw [same]
    exact ready.semantic.1.normal.facts.cached.nodes event.key event.candidate selected
  exact SourceCurrentWriterFiniteNodeAlignment.writer writer selected expressions rfl depth
    (fun current rowIndex symbol guard originals found childIndex child childFound _ =>
      children depth current rowIndex symbol guard originals found childIndex child childFound)
    ready event.result available

/-- A retained node writer with a nested used binder applies the finite child step at every observation depth. -/
theorem witness :
    (build source [] empty = .done event.result reader ∧ Ready reader ∧
      Writer reader event.key event.candidate event ∧
      build (.binder true requester) [] reader = .done event.result reader ∧
      requester ≠ event.expression ∧
      InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
      nestedUsed = true ∧ ¬ InternedStoredShallowCompletion.BinderFree event.expression) ∧
    ∀ depth, SourceCurrentWriterFiniteNodeAlignment.ReconstructionAt (depth + 1)
      event.entry event.body event.depth event.ordinary event.result reader := witness_proof

end MicroCFTA.WriterSourceReviewKernels
