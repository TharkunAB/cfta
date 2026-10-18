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

namespace MicroCFTA.FilteredRootReview
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


private theorem node_plain (expressions : List (EdgeSyntax Nat Bool))
    (inputs : List (Value Nat Bool)) (before after : State Nat Bool)
    (context : InternedFreshOrdinaryContext.Context before inputs)
    (result : Value Nat Bool) (actual : build (.node expressions) inputs before = .done result after) :
    SourceEqualityRequiredCache.Ordinary result := by
  cases called : buildEdges expressions inputs before with
  | pending key middle => simp only [build,called,Outcome.bind] at actual; cases actual
  | done rows middle =>
      have made := Outcome.done.inj (by simpa only [build,called,Outcome.bind,InternedNestedConstruction.work] using actual)
      have checked := InternedFreshOrdinaryFacts.buildEdges_verified expressions inputs before context.normal.facts context.inputs
      have facts : InternedNestedFacts.Facts middle := by simpa only [called,Outcome.state] using checked.facts
      have plain := SourceEqualityRequiredCache.node_ordinary rows middle facts (checked.result rows middle called)
      rw [made.1] at plain
      exact plain

private theorem warm (depth : Nat) (view common : State Nat Bool)
    (current : Keeps event.afterBody common)
    (firstValue secondValue : Value Nat Bool)
    (firstAvailable : Available common firstValue) (secondAvailable : Available common secondValue)
    (related : RelatedAt depth view firstValue secondValue) (left right : Value Nat Bool)
    (firstDone : execute event.body (bind (.interned event.entry.identity) firstValue (fun _ => none)) common = .done left common)
    (secondDone : execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) secondValue (fun _ => none)) common = .done right common) :
    RelatedAt (depth + 1) view left right := by
  obtain ⟨depthContext,cutContext,bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have ordinaryInputs := depthContext.base.local (.uninterned (ordinaryLevel event.depth))
    (InternedNestedProvenance.ordinary_available _ _)
  have argument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have bodyInputs := bodyContext.base.local (.interned event.entry.identity) argument
  have checked := callback_verified event.expression event.environment (.interned event.entry.identity)
    event.allocated bodyInputs.normal.facts bodyInputs.inputs
  have actual : callback event.expression event.environment (.interned event.entry.identity) event.allocated =
      .done event.body event.afterBody := event.bodyDone
  have argumentEnd : Available event.afterBody (.reference (.interned event.entry.identity)) := by
    simpa only [actual,Outcome.state] using checked.available _ argument
  have captures : Values event.afterBody event.environment := by
    intro value member
    simpa only [actual,Outcome.state] using checked.available value (bodyContext.base.inputs value member)
  have firstInputs : Values common (.reference (.interned event.entry.identity) :: event.environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact current.available _ argumentEnd
    · exact current.available _ (captures _ member)
  have secondInputs : Values common (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact InternedNestedProvenance.ordinary_available _ _
    · exact current.available _ (captures _ member)
  obtain ⟨firstRaw,secondRaw,cutGrowth⟩ := SourceCurrentWriterFiniteNodeAlignment.raw_calls event expressions rfl
  have firstWarm := InternedFreshOrdinaryReplay.build_replay (.node expressions) _ event.allocated common
    event.body event.afterBody bodyInputs.normal.facts.coherent.valid firstRaw current.growth
  have secondWarm := InternedFreshOrdinaryReplay.build_replay (.node expressions) _ event.afterDepth common
    event.ordinary event.cut depthContext.base.normal.facts.coherent.valid secondRaw (grows_trans cutGrowth current.growth)
  have bodyAvailable := (build_verified (.node expressions) _ common current.ready.semantic.1.normal.facts firstInputs).result
    event.body common firstWarm
  have ordinaryAvailable := (build_verified (.node expressions) _ common current.ready.semantic.1.normal.facts secondInputs).result
    event.ordinary common secondWarm
  let environment := shared event firstValue secondValue (fun _ => none)
  have replacements : Replacements common environment := by
    intro name value found
    dsimp only [environment,shared,SourceCurrentStoredMuBinderChildLineage.bind] at found
    split at found
    · cases found; exact firstAvailable
    · split at found
      · cases found; exact secondAvailable
      · cases found
  have substitutions := SourceCurrentPublicationSharedReplacements.substitutions event firstValue secondValue
    (fun _ => none) common current.ready.semantic.1.normal.facts.coherent bodyAvailable ordinaryAvailable
  have firstShared : execute event.body environment common = .done left common := by
    rw [← substitutions.1]
    exact firstDone
  have secondShared : execute event.ordinary environment common = .done right common := by
    rw [← substitutions.2]
    exact secondDone
  have paired := SourceCurrentPublicationSharedReplacements.paired event (RelatedAt depth view)
    (fun value => ⟨Iff.rfl,SourceCurrentOpenObservations.Same.refl depth view [value]⟩)
    firstValue secondValue (fun _ => none) related

  have matched := SourceCurrentFiniteRootSourceNode.node expressions event.environment
    (.interned event.entry.identity) (.uninterned (ordinaryLevel event.depth)) depth view common
    (fun rowIndex symbol guard originals found childIndex child childFound _ =>
      children depth view common rowIndex symbol guard originals found childIndex child childFound)
    environment environment paired current.ready firstInputs secondInputs replacements replacements
    event.allocated event.afterBody event.afterDepth event.cut bodyInputs ordinaryInputs
    event.body event.ordinary firstRaw secondRaw current.growth (grows_trans cutGrowth current.growth)
    (fun _ _ => False)
  have plain := node_plain expressions _ event.allocated event.afterBody bodyInputs event.body firstRaw
  have noAtoms (atom : Value Nat Bool) (found : Literal event.body atom) : False := by
    generalize shape : event.body = raw at plain found
    cases raw <;> try {cases plain} <;> cases found
  have comparison := SourceCurrentFiniteRootReconstruction.reconstruct depth view common
    (fun _ _ => False) (SourceCurrentFiniteRootReconstruction.Executions depth view common environment environment)
    environment environment event.body event.ordinary current.ready bodyAvailable ordinaryAvailable
    replacements replacements matched (by intro _ _ impossible; cases impossible)
    (by intro a b found _ _; exact False.elim (noAtoms a found))
    (by intro a b hypothesis; exact hypothesis)
  exact comparison left right firstShared secondShared

private theorem reconstruction (depth : Nat) (view : State Nat Bool) :
    ∃ left middle right final,
      execute event.body (bind (.interned event.entry.identity) event.result (fun _ => none)) reader = .done left middle ∧
      execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) event.result (fun _ => none)) middle = .done right final ∧
      execute event.body (bind (.interned event.entry.identity) event.result (fun _ => none)) final = .done left final ∧
      execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) event.result (fun _ => none)) final = .done right final ∧
      Keeps reader middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Nonempty (History reader middle) ∧ Nonempty (History middle final) ∧
      RelatedAt (depth+1) view left right := by
  have available : Available reader event.result := by
    have same : event.result = event.candidate := by cbv
    rw [same]
    exact ready.semantic.1.normal.facts.cached.nodes event.key event.candidate selected
  obtain ⟨left,middle,right,final,firstDone,secondDone,firstKept,secondKept,leftAvailable,rightAvailable,
    firstHistory,secondHistory,_⟩ := SourceCurrentStoredReconstruction.mu event.key event.entry
      event.body event.depth event.ordinary event.result reader ready selected available
  have firstWarm := InternedFreshOrdinaryReplay.build_replay (encode (leaves event.body) [] event.body)
    ((leaves event.body).map (InternedStoredSubstitution.input (bind (.interned event.entry.identity) event.result (fun _ => none))))
    reader final left middle ready.semantic.1.normal.facts.coherent.valid firstDone secondKept.growth
  have secondWarm := InternedFreshOrdinaryReplay.build_replay (encode (leaves event.ordinary) [] event.ordinary)
    ((leaves event.ordinary).map (InternedStoredSubstitution.input
      (bind (.uninterned (ordinaryLevel event.depth)) event.result (fun _ => none))))
    middle final right final firstKept.ready.semantic.1.normal.facts.coherent.valid secondDone (grows_refl _)
  have initial : Keeps event.afterBody reader := ⟨ready,writer.2.2.2.2.2.2.2.1,writer.2.2.2.2.2.2.2.2⟩
  have finalCurrent := initial.trans (firstKept.trans secondKept)
  have finalAvailable := secondKept.available event.result (firstKept.available event.result available)
  have related := warm depth view final finalCurrent event.result event.result finalAvailable finalAvailable
    ⟨Iff.rfl,SourceCurrentOpenObservations.Same.refl depth view [event.result]⟩ left right firstWarm secondWarm
  exact ⟨left,middle,right,final,firstDone,secondDone,firstWarm,secondWarm,firstKept,secondKept,
    leftAvailable,rightAvailable,firstHistory,secondHistory,related⟩

private theorem witness_proof :
    (build source [] empty = .done event.result reader ∧ Ready reader ∧
      Writer reader event.key event.candidate event ∧
      build (.binder true requester) [] reader = .done event.result reader ∧
      requester ≠ event.expression ∧
      InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
      nestedUsed = true ∧ ¬ InternedStoredShallowCompletion.BinderFree event.expression) ∧
    ∀ depth view, ∃ left middle right final,
      execute event.body (bind (.interned event.entry.identity) event.result (fun _ => none)) reader = .done left middle ∧
      execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) event.result (fun _ => none)) middle = .done right final ∧
      execute event.body (bind (.interned event.entry.identity) event.result (fun _ => none)) final = .done left final ∧
      execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) event.result (fun _ => none)) final = .done right final ∧
      Keeps reader middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Nonempty (History reader middle) ∧ Nonempty (History middle final) ∧
      RelatedAt (depth+1) view left right := ⟨source_checks,reconstruction⟩

/-- A selected earlier node writer with a closed used-Mu child derives root matching and both actual finite reconstructions. -/
theorem witness :
    (build source [] empty = .done event.result reader ∧ Ready reader ∧
      Writer reader event.key event.candidate event ∧
      build (.binder true requester) [] reader = .done event.result reader ∧
      requester ≠ event.expression ∧
      InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
      nestedUsed = true ∧ ¬ InternedStoredShallowCompletion.BinderFree event.expression) ∧
    ∀ depth view, ∃ left middle right final,
      execute event.body (bind (.interned event.entry.identity) event.result (fun _ => none)) reader = .done left middle ∧
      execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) event.result (fun _ => none)) middle = .done right final ∧
      execute event.body (bind (.interned event.entry.identity) event.result (fun _ => none)) final = .done left final ∧
      execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) event.result (fun _ => none)) final = .done right final ∧
      Keeps reader middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Nonempty (History reader middle) ∧ Nonempty (History middle final) ∧
      RelatedAt (depth+1) view left right := witness_proof

end MicroCFTA.FilteredRootReview
