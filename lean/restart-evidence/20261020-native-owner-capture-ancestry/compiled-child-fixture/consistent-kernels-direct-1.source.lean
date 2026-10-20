import MicroCFTA.SourceCurrentNativeOptionalChildOrigin
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.SourceCurrentConjunctionFieldAllocation
import MicroCFTA.SourceCurrentNativeMuPublication

/-!
# A source-built pair retains the same queried owner at its optional site

Both operands are actual raw Mu results. The admitted prefix starts at a
node query. It stops at the compiled optional instruction before that
instruction executes or the owner returns. Physical cache validity and
initial publication history come from the actual source builds. An actual Top-field
allocation supplies the initial loaded field. The actual child returns Empty.
-/
noncomputable section
namespace MicroCFTA.NativeConsistentOwnerFixture
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

private def allocatedOps :=
  SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty

private def firstSource : Syntax Symbol Guard := .binder false (.union [])
private def secondSource : Syntax Symbol Guard :=
  .binder false (.node [.mk ("leaf",.top) SourceEqualityConstraintConstructors.top []])
private def firstBuilt := InternedFreshOrdinaryConstruction.build firstSource [] (empty : Heap)
private def left : Node := .mu ⟨0,.mu ⟨.empty,.empty⟩⟩ .empty .empty .empty
private def firstHeap : Heap := firstBuilt.state
private def secondBuilt := InternedFreshOrdinaryConstruction.build secondSource [] firstHeap
private def leaf : Node := .node ⟨1,.node [0]⟩
  [.mk ⟨0,⟨("leaf",.top),[],SourceEqualityConstraintConstructors.top⟩⟩ []] 0 []
private def right : Node := .mu ⟨2,.mu ⟨.node 1,.node 1⟩⟩ leaf leaf leaf
private def heap : Heap := secondBuilt.state
private def before : Checked 8 :=
  ⟨initial 8 ⟨heap,Cache.emptyState⟩,allocatedOps⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
private def first : Nat := (SourceRecursiveIntersectionControl.identity left).getD 0
private def second : Nat := (SourceRecursiveIntersectionControl.identity right).getD 0
private def pair := SourceRecursiveIntersectionControl.pair first second
private def finish (value : Node) : Code Symbol Guard Node := .finishNode 0 value (.pure value)
private def compilerBefore : Checked 8 := (step (.code (requestNode request.domain left right)) before).state
private def entered := SourceRecursiveIntersectionEnvironment.enter compilerBefore.native.machine.domains
  request.domain.key left right first second
private def childBefore : Checked 8 :=
  {compilerBefore with native := advance compilerBefore.native {compilerBefore.native.machine with domains := entered.2}}
private def child : NodeRequest Symbol Guard := ⟨entered.1,body left,body right⟩
private def childNext (value : Node) : Code Symbol Guard Node := .optionalBinder pair value finish

private def siteBefore : Checked 8 := (step (.code (.node child childNext)) childBefore).state

private theorem first_done : firstBuilt = .done left firstHeap := by cbv
private theorem second_done : secondBuilt = .done right heap := by cbv
private theorem shapes : (∃ entry stored depth ordinary, left = .mu entry stored depth ordinary) ∧
    (∃ entry stored depth ordinary, right = .mu entry stored depth ordinary) ∧ left ≠ right := by
  constructor
  · exact ⟨_,_,_,_,rfl⟩
  constructor
  · exact ⟨_,_,_,_,rfl⟩
  · intro same
    have identities := congrArg SourceRecursiveIntersectionControl.identity same
    change some 0 = some 2 at identities
    cases identities
private theorem decision : SourceRecursiveIntersectionControl.decision request.domain.key left right = .bothMu := by cbv
private theorem first_available : Available firstHeap left :=
  (InternedFreshOrdinaryFacts.build_verified firstSource [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result left firstHeap first_done
private theorem first_facts : InternedNestedFacts.Facts firstHeap :=
  (InternedFreshOrdinaryFacts.build_verified firstSource [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).facts
private theorem second_available : Available heap right :=
  (InternedFreshOrdinaryFacts.build_verified secondSource [] firstHeap first_facts
    (by intro value member; cases member)).result right heap second_done
private theorem left_available : Available heap left := by
  have checked := InternedFreshOrdinaryFacts.build_verified secondSource [] firstHeap first_facts
    (by intro value member; cases member)
  exact first_available.grows firstHeap heap checked.growth checked.history
private theorem semantic : SemanticHeap heap :=
  SourceRecursiveIntersectionSemanticHeap.source secondSource [] firstHeap
    (SourceRecursiveIntersectionSemanticHeap.source firstSource [] empty
      SourceRecursiveIntersectionSemanticHeap.empty_heap (by intro value member; cases member))
    (by intro value member; cases member)
private theorem query_inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs
    (.code (requestNode request.domain left right)) before := by
  refine ⟨⟨empty_domain _,left_available,second_available⟩,?_⟩
  intro key actual
  exact ⟨by decide,by decide,.mu 0,.mu 2,rfl,rfl,by unfold IntersectionFlatMemoKey.Safe IntersectionFlatMemoKey.code; decide,by unfold IntersectionFlatMemoKey.Safe IntersectionFlatMemoKey.code; decide⟩
private theorem enter_inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs
    (.code ((compileNode request).bind finish)) compilerBefore := by
  have selected : compileNode request = compileMu request.domain left right := by cbv
  rw [selected]
  change Domain compilerBefore.native.machine request.domain ∧ Available heap left ∧ Available heap right
  exact ⟨empty_domain _,left_available,second_available⟩
private theorem child_inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs
    (.code (.node child childNext)) childBefore := by
  have valid : SourceRecursiveIntersectionKernel.Valid compilerBefore.native.machine :=
    ⟨(InternedFreshOrdinaryFacts.build_verified secondSource [] firstHeap first_facts
      (by intro value member; cases member)).facts,Cache.empty_valid⟩
  have known := (SourceRecursiveIntersectionKernel.entered compilerBefore.native.machine valid request.domain (empty_domain _) left right
    left_available second_available first second).2.2
  refine ⟨⟨known,?_,?_⟩,?_⟩
  · change Available heap .empty
    exact empty_available _
  · change Available heap (body right)
    exact body_available heap right second_available
  · intro key actual
    exact ⟨by decide,by cbv,.empty,.node 1,rfl,rfl,True.intro,by unfold IntersectionFlatMemoKey.Safe IntersectionFlatMemoKey.code; decide⟩
private theorem query_step : step (.code (requestNode request.domain left right)) before =
    .yielded (.code ((compileNode request).bind finish)) compilerBefore := by cbv
private theorem enter_step : step (.code ((compileNode request).bind finish)) compilerBefore =
    .yielded (.code (.node child childNext)) childBefore := by cbv
private theorem child_step : step (.code (.node child childNext)) childBefore =
    .yielded (.code (.finishNode 1 .empty (.optionalBinder pair .empty finish))) siteBefore := by cbv
private theorem finish_inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs
    (.code (.finishNode 1 .empty (.optionalBinder pair .empty finish))) siteBefore := by
  refine ⟨child,?_,empty_available _⟩
  cbv
private theorem finish_step : step (.code (.finishNode 1 .empty (.optionalBinder pair .empty finish))) siteBefore =
    .yielded (.code (.optionalBinder pair .empty finish))
      ⟨SourceRecursiveIntersectionThunks.finishNode 1 .empty siteBefore.native,siteBefore.operations⟩ := by rfl
private def after : Checked 8 :=
  ⟨SourceRecursiveIntersectionThunks.finishNode 1 .empty siteBefore.native,siteBefore.operations⟩
private theorem actual : Trace 4 (.code (requestNode request.domain left right)) before
    (.code (.optionalBinder pair .empty finish)) after := by
  exact .cons _ _ _ _ _ _ 3 query_inputs query_step
    (.cons _ _ _ _ _ _ 2 enter_inputs enter_step
      (.cons _ _ _ _ _ _ 1 child_inputs child_step
        (.cons _ _ _ _ _ _ 0 finish_inputs finish_step (.refl _ _))))

private theorem physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native := by
  apply SourceCurrentAllocatedNativePhysicalCache.initial_valid
  exact ⟨(InternedFreshOrdinaryFacts.build_verified secondSource [] firstHeap first_facts
    (by intro value member; cases member)).facts, Cache.empty_valid⟩

private theorem first_context : SourceCurrentConstrainedCapSourceHistory.Context firstHeap [] :=
  SourceCurrentConstrainedCapSourceHistory.empty_context.build firstSource

private theorem publication_history : Nonempty (SourceCurrentNativeMuPublication.History empty heap) := by
  exact ⟨.trans (SourceCurrentNativeMuPublication.closed_history firstSource)
    (Classical.choice (SourceCurrentNativeMuPublication.build_history secondSource [] firstHeap first_context))⟩

private theorem ready : SourceEqualityRequiredCache.Ready heap := by
  refine ⟨semantic, ?_, ?_⟩
  · exact InternedFreshOrdinaryCoverage.build_covered secondSource [] firstHeap
      first_facts.coherent.valid
      (InternedFreshOrdinaryCoverage.closed_covered firstSource left firstHeap first_done)
      right heap second_done
  · exact (InternedOpenDepthExecution.build_depth secondSource [] firstHeap first_context.base
      first_context.depth (InternedOpenDepthExecution.closed_heap firstSource)).heap

private theorem operation_valid : SourceEqualityConstraintMemoAllocation.Valid allocatedOps :=
  (SourceCurrentConjunctionFieldAllocation.empty_field SourceEqualityConstraintMemoAllocation.empty
    SourceEqualityConstraintMemoAllocation.empty_valid).1

private theorem top_field : SourceCurrentConjunctionEquality.FieldAvailable allocatedOps
    (SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)) :=
  (SourceCurrentConjunctionFieldAllocation.empty_field SourceEqualityConstraintMemoAllocation.empty
    SourceEqualityConstraintMemoAllocation.empty_valid).2.2

private theorem fields : SourceCurrentConjunctionEquality.Fields allocatedOps heap := by
  exact SourceEqualityAnnotationConstruction.build _ secondSource
    (by exact ⟨top_field,True.intro,True.intro⟩) [] firstHeap
    (SourceEqualityAnnotationConstruction.build _ firstSource True.intro [] empty
      (SourceEqualityAnnotationHeap.empty_heap _))

private theorem good : SourceCurrentAllocatedNativePhysicalCompletion.Good before :=
  ⟨physical,ready,operation_valid,fields⟩

private theorem history : SourceCurrentNativeEdgeWriterGrowth.History before :=
  .initial _ _

private theorem site_owner (handle : Nat) (queried : NodeRequest Symbol Guard)
    (present : after.native.nodes.cells handle = some ⟨queried,.evaluating⟩) :
    queried = request := by
  cases handle with
  | zero =>
      change some ⟨request,.evaluating⟩ = some ⟨queried,.evaluating⟩ at present
      exact (congrArg FlatMemoThunk.Cell.request (Option.some.inj present)).symm
  | succ handle =>
      cases handle with
      | zero =>
          change some ⟨child,.returned .empty⟩ = some ⟨queried,.evaluating⟩ at present
          cases present
      | succ handle =>
          change none = some ⟨queried,.evaluating⟩ at present
          cases present

private theorem checked_witness :
    allocatedOps = SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty ∧
    firstBuilt = .done left firstHeap ∧ secondBuilt = .done right heap ∧
    (∃ entry stored depth ordinary, left = .mu entry stored depth ordinary) ∧
    (∃ entry stored depth ordinary, right = .mu entry stored depth ordinary) ∧
    left ≠ right ∧ SourceRecursiveIntersectionControl.decision request.domain.key left right = .bothMu ∧
    SemanticHeap heap ∧ Available heap left ∧ Available heap right ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good before ∧
    SourceCurrentNativeEdgeWriterGrowth.History before ∧
    Nonempty (SourceCurrentNativeMuPublication.History empty heap) ∧
    Trace 4 (.code (requestNode request.domain left right)) before
      (.code (.optionalBinder pair .empty finish)) after ∧
    ∃ (queryFuel childFuel : Nat) (queried : NodeRequest Symbol Guard)
        (callerNext : Node → Code Symbol Guard Node) (queryBefore : Checked 8)
        (handle : Nat) (chosen running : SourceRecursiveIntersectionThunks.State 8 Symbol Guard)
        (first second : Nat),
      let compilerBefore : Checked 8 := ⟨running, queryBefore.operations⟩
      let entered := SourceRecursiveIntersectionEnvironment.enter compilerBefore.native.machine.domains
        queried.domain.key queried.left queried.right first second
      let childBefore : Checked 8 :=
        {compilerBefore with native := advance compilerBefore.native {compilerBefore.native.machine with domains := entered.2}}
      4 = queryFuel + 2 + childFuel ∧
      Trace queryFuel (.code (requestNode request.domain request.left request.right)) before
        (.code (.node queried callerNext)) queryBefore ∧
      Inputs (.code (.node queried callerNext)) queryBefore ∧
      lookupNode 8 queried queryBefore.native = (.memoized handle, chosen) ∧
      demandNode handle chosen = (.evaluate queried, running) ∧
      chosen.nodes.cells handle = some ⟨queried, .suspended⟩ ∧
      running.nodes.cells handle = some ⟨queried, .evaluating⟩ ∧
      running.machine = queryBefore.native.machine ∧
      step (.code (.node queried callerNext)) queryBefore = .yielded
        (.code ((compileNode queried).bind (fun value => .finishNode handle value (callerNext value)))) compilerBefore ∧
      (SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .bothMu ∨
        SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .leftMu ∨
        SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .rightMu) ∧
      SourceRecursiveIntersectionControl.identity queried.left = some first ∧
      SourceRecursiveIntersectionControl.identity queried.right = some second ∧
      pair = SourceRecursiveIntersectionControl.pair first second ∧
      Inputs (.code (compileMu queried.domain queried.left queried.right)) compilerBefore ∧
      step (.code (compileMu queried.domain queried.left queried.right)) compilerBefore =
        .yielded (.code ((requestNode entered.1 (body queried.left) (body queried.right)).bind
          (fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure))) childBefore ∧
      Trace childFuel (.code (requestNode entered.1 (body queried.left) (body queried.right)))
        childBefore (.code (.pure .empty)) after ∧
      (finish = fun value => .finishNode handle value (callerNext value)) ∧
      after.native.nodes.cells handle = some ⟨queried, .evaluating⟩ ∧
      Forwarded after ⟨entered.1,body queried.left,body queried.right⟩ childBefore after .empty
 ∧
      ∃ childHandle, after.native.nodes.cells childHandle =
        some ⟨⟨entered.1,body queried.left,body queried.right⟩,.returned .empty⟩ ∧
        SourceCurrentNativeWriterReadyRetention.Written (width := 8) childHandle
          ⟨entered.1,body queried.left,body queried.right⟩ .empty after.native := by
  obtain ⟨queryFuel,childFuel,queried,callerNext,queryBefore,handle,chosen,running,
    first,second,total,earlier,inputs,selected,demanded,suspended,evaluating,machine,
    queryStep,recursive,leftIdentity,rightIdentity,pairEq,enterInputs,enterStep,
    childTrace,continuation,retained,forwarded⟩ :=
    SourceCurrentNativeOptionalChildOrigin.request request 4 before after pair .empty finish good history actual
  let compiler : Checked 8 := ⟨running,queryBefore.operations⟩
  let localDomain := SourceRecursiveIntersectionEnvironment.enter compiler.native.machine.domains
    queried.domain.key queried.left queried.right first second
  have same : queried = request := site_owner handle queried retained
  have keyed : SourceRecursiveIntersectionMemo.requestKey 8 localDomain.1
      (body queried.left) (body queried.right) ≠ none := by
    rw [same]
    unfold SourceRecursiveIntersectionMemo.requestKey
    rw [IntersectionFlatMemoKeyDomain.sourceKey_complete 8 _ _ _ .empty (.node 1) rfl rfl]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  obtain ⟨childHandle,childCell,childWriter⟩ := forwarded.2.resolve_left (fun direct => keyed direct.1)
  exact ⟨rfl,first_done,second_done,shapes.1,shapes.2.1,shapes.2.2,decision,
    semantic,left_available,second_available,good,history,publication_history,actual,
    queryFuel,childFuel,queried,callerNext,queryBefore,handle,chosen,running,
    first,second,total,earlier,inputs,selected,demanded,suspended,evaluating,machine,
    queryStep,recursive,leftIdentity,rightIdentity,pairEq,enterInputs,enterStep,
    childTrace,continuation,retained,forwarded,childHandle,childCell,childWriter⟩

/-- Actual source construction supplies the same active owner and its keyed child writer. -/
theorem actual_consistent_site :
    allocatedOps = SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty ∧
    firstBuilt = .done left firstHeap ∧ secondBuilt = .done right heap ∧
    (∃ entry stored depth ordinary, left = .mu entry stored depth ordinary) ∧
    (∃ entry stored depth ordinary, right = .mu entry stored depth ordinary) ∧
    left ≠ right ∧ SourceRecursiveIntersectionControl.decision request.domain.key left right = .bothMu ∧
    SemanticHeap heap ∧ Available heap left ∧ Available heap right ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good before ∧
    SourceCurrentNativeEdgeWriterGrowth.History before ∧
    Nonempty (SourceCurrentNativeMuPublication.History empty heap) ∧
    Trace 4 (.code (requestNode request.domain left right)) before
      (.code (.optionalBinder pair .empty finish)) after ∧
    ∃ (queryFuel childFuel : Nat) (queried : NodeRequest Symbol Guard)
        (callerNext : Node → Code Symbol Guard Node) (queryBefore : Checked 8)
        (handle : Nat) (chosen running : SourceRecursiveIntersectionThunks.State 8 Symbol Guard)
        (first second : Nat),
      let compilerBefore : Checked 8 := ⟨running, queryBefore.operations⟩
      let entered := SourceRecursiveIntersectionEnvironment.enter compilerBefore.native.machine.domains
        queried.domain.key queried.left queried.right first second
      let childBefore : Checked 8 :=
        {compilerBefore with native := advance compilerBefore.native {compilerBefore.native.machine with domains := entered.2}}
      4 = queryFuel + 2 + childFuel ∧
      Trace queryFuel (.code (requestNode request.domain request.left request.right)) before
        (.code (.node queried callerNext)) queryBefore ∧
      Inputs (.code (.node queried callerNext)) queryBefore ∧
      lookupNode 8 queried queryBefore.native = (.memoized handle, chosen) ∧
      demandNode handle chosen = (.evaluate queried, running) ∧
      chosen.nodes.cells handle = some ⟨queried, .suspended⟩ ∧
      running.nodes.cells handle = some ⟨queried, .evaluating⟩ ∧
      running.machine = queryBefore.native.machine ∧
      step (.code (.node queried callerNext)) queryBefore = .yielded
        (.code ((compileNode queried).bind (fun value => .finishNode handle value (callerNext value)))) compilerBefore ∧
      (SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .bothMu ∨
        SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .leftMu ∨
        SourceRecursiveIntersectionControl.decision queried.domain.key queried.left queried.right = .rightMu) ∧
      SourceRecursiveIntersectionControl.identity queried.left = some first ∧
      SourceRecursiveIntersectionControl.identity queried.right = some second ∧
      pair = SourceRecursiveIntersectionControl.pair first second ∧
      Inputs (.code (compileMu queried.domain queried.left queried.right)) compilerBefore ∧
      step (.code (compileMu queried.domain queried.left queried.right)) compilerBefore =
        .yielded (.code ((requestNode entered.1 (body queried.left) (body queried.right)).bind
          (fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure))) childBefore ∧
      Trace childFuel (.code (requestNode entered.1 (body queried.left) (body queried.right)))
        childBefore (.code (.pure .empty)) after ∧
      (finish = fun value => .finishNode handle value (callerNext value)) ∧
      after.native.nodes.cells handle = some ⟨queried, .evaluating⟩ ∧
      Forwarded after ⟨entered.1,body queried.left,body queried.right⟩ childBefore after .empty
 ∧
      ∃ childHandle, after.native.nodes.cells childHandle =
        some ⟨⟨entered.1,body queried.left,body queried.right⟩,.returned .empty⟩ ∧
        SourceCurrentNativeWriterReadyRetention.Written (width := 8) childHandle
          ⟨entered.1,body queried.left,body queried.right⟩ .empty after.native := checked_witness

end MicroCFTA.NativeConsistentOwnerFixture
