import MicroCFTA.SourceCurrentNativeReaderRowLineage
import MicroCFTA.SourceCurrentNativeWriterChildOrigins
import MicroCFTA.SourceEqualityNativeDemandMismatchProvenance
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.SourceEqualityAnnotationConstruction
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
noncomputable section
namespace MicroCFTA.ReaderRowLineageIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceCurrentNativeRowOrigins
open SourceCurrentNativeEdgeHistory (Writer)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def top : Guard := SourceEqualityConstraintConstructors.top
private def leaf : Syntax Symbol Guard := .node [.mk ("same",.top) top []]
private def productive : Syntax Symbol Guard := .binder false (.node [
  .mk ("same",.top) top [], .mk ("same",.top) top [.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("same",.top) top [leaf,productive]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private theorem constructed : built = .done root heap := by cbv
private def first : Node := ((children root)[0]?).getD .empty
private def mu : Node := ((children root)[1]?).getD .empty
private def row : EdgeValue Symbol Guard := match root with
  | .node _ (edge :: _) _ _ => edge
  | _ => (run (makeEdge ("fallback",.top) top []) empty).1
private theorem row_children : row.children = [first,mu] := by cbv
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def operations := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def before : Checked 8 := ⟨initial 8 machine,operations⟩
private def domain := IntersectionEmptyDomain.emptyDomain
private def request : EdgeRequest Symbol Guard := ⟨domain,row,row⟩
private theorem initial_good : Good before := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression,leaf,productive,SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed,SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built,heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
    ⟨semantic.ready.semantic.1.normal.facts,Cache.empty_valid⟩,semantic.ready,loaded.1,?_⟩
  intro key edge found
  have same := guarded key edge found
  rw [same]
  exact loaded.2.2

private theorem mu_available : Available heap mu :=
  ((InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed).children mu (by cbv; exact .tail _ (.head _))
private theorem first_available : Available heap first :=
  ((InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed).children first (by cbv; exact .head _)
private theorem row_resident : EdgeResident heap row := by
  have original := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  exact resident_edges heap initial_good.heap.semantic.1.normal.facts.linked root original.resident row (by cbv; exact .head _)
private theorem edge_ready : EdgeReady machine request := ⟨empty_domain machine,row_resident,row_resident⟩
private theorem mu_ready : NodeReady machine ⟨domain,mu,mu⟩ := ⟨empty_domain machine,mu_available,mu_available⟩
private theorem mu_safe : SourceRecursiveIntersectionMemo.KeySafe 8 domain mu mu := by
  unfold SourceRecursiveIntersectionMemo.KeySafe
  refine ⟨by decide,by cbv,.mu 3,.mu 3,?_,?_,?_,?_⟩ <;> cbv

private def allocated : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula := ⟨.live 0 [],.top⟩
private def selectedEdge := (lookupEdge 8 request before.native).2
private def runningEdge := (demandEdge 0 selectedEdge).2
private def edgeStarted : Checked 8 := ⟨runningEdge,operations⟩
private def checkedOps := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le allocated allocated 2 2 operations).2
private def checkedEdge : Checked 8 := ⟨runningEdge,checkedOps⟩
private def firstChosen := (lookupNode 8 ⟨domain,first,first⟩ checkedEdge.native).2
private def firstRunning := (demandNode 0 firstChosen).2
private def firstStarted : Checked 8 := ⟨firstRunning,checkedOps⟩
private def afterFirst : Checked 8 := ⟨SourceRecursiveIntersectionThunks.finishNode 0 first firstRunning,checkedOps⟩
private def muChosen := (lookupNode 8 ⟨domain,mu,mu⟩ afterFirst.native).2
private def muRunning := (demandNode 1 muChosen).2
private def muStarted : Checked 8 := ⟨muRunning,checkedOps⟩
private def afterMu : Checked 8 := ⟨SourceRecursiveIntersectionThunks.finishNode 1 mu muRunning,checkedOps⟩
private theorem first_started_heap : firstStarted.native.machine.heap = heap := by cbv
private theorem after_first_heap : afterFirst.native.machine.heap = heap := by cbv
private theorem mu_started_heap : muStarted.native.machine.heap = heap := by cbv
private theorem after_mu_heap : afterMu.native.machine.heap = heap := by cbv
private theorem first_safe : SourceRecursiveIntersectionMemo.KeySafe 8 domain first first := by
  unfold SourceRecursiveIntersectionMemo.KeySafe
  refine ⟨by decide,by cbv,.node 0,.node 0,?_,?_,?_,?_⟩ <;> cbv
private theorem first_call : Trace 2 (.code (requestNode domain first first)) checkedEdge (.code (.pure first)) afterFirst := by
  refine Trace.cons (.code (requestNode domain first first)) checkedEdge
    (.code (.finishNode 0 first (.pure first))) firstStarted (.code (.pure first)) afterFirst 1 ?_ ?_ ?_
  · exact ⟨⟨empty_domain _,first_available,first_available⟩,by intro key found; exact first_safe⟩
  · cbv
  · refine Trace.cons (.code (.finishNode 0 first (.pure first))) firstStarted
      (.code (.pure first)) afterFirst (.code (.pure first)) afterFirst 0 ?_ rfl (.refl _ _)
    refine ⟨⟨domain,first,first⟩,by cbv,?_⟩
    rw [first_started_heap]
    exact first_available
private theorem mu_call : Trace 2 (.code (requestNode domain mu mu)) afterFirst (.code (.pure mu)) afterMu := by
  refine Trace.cons (.code (requestNode domain mu mu)) afterFirst
    (.code (.finishNode 1 mu (.pure mu))) muStarted (.code (.pure mu)) afterMu 1 ?_ ?_ ?_
  · refine ⟨⟨empty_domain _,?_,?_⟩,by intro key found; exact mu_safe⟩ <;>
      (rw [after_first_heap]; exact mu_available)
  · cbv
  · refine Trace.cons (.code (.finishNode 1 mu (.pure mu))) muStarted
      (.code (.pure mu)) afterMu (.code (.pure mu)) afterMu 0 ?_ rfl (.refl _ _)
    refine ⟨⟨domain,mu,mu⟩,by cbv,?_⟩
    rw [mu_started_heap]
    exact mu_available
private def madeEdge : Checked 8 := ⟨advance afterMu.native {afterMu.native.machine with heap := (run (makeEdge row.entry.key.symbol top [first,mu]) heap).2},checkedOps⟩
private def edgeAfter : Checked 8 := ⟨SourceRecursiveIntersectionThunks.finishEdge 0 row madeEdge.native,checkedOps⟩
private theorem made_edge_heap : madeEdge.native.machine.heap = heap := by cbv
private theorem edge_after_machine : edgeAfter.native.machine = machine := by cbv
private theorem cold_edge : Trace 8 (.code (requestEdge domain row row)) before (.code (.pure row)) edgeAfter := by
  have one : step (.code (requestEdge domain row row)) before = .yielded
      ((Control.edgeBody request .pure).bind (fun value => .finishEdge 0 value (.pure value))) edgeStarted := by cbv
  have bodyStep : step (.edgeBody request .pure) edgeStarted = .yielded
      (.code (SourceEqualityNativeCheckedCode.children domain row row allocated)) checkedEdge := by cbv
  have walked : SourceCurrentAllocatedNativeSemanticTraceReadback.Walk
      (fun pair : Node × Node => requestNode domain pair.1 pair.2)
      [(first,first),(mu,mu)] checkedEdge [first,mu] afterMu 4 :=
    .cons (call := fun pair : Node × Node => requestNode domain pair.1 pair.2)
      (first,first) [(mu,mu)] checkedEdge afterFirst afterMu first [mu] 2 2 first_call
      (.cons (mu,mu) [] afterFirst afterMu afterMu mu [] 2 0 mu_call (.nil _))
  have made : Trace 1 (.code (.work (makeEdge row.entry.key.symbol top [first,mu]) .pure))
      afterMu (.code (.pure row)) madeEdge := by
    refine Trace.cons (.code (.work (makeEdge row.entry.key.symbol top [first,mu]) .pure))
      afterMu (.code (.pure row)) madeEdge (.code (.pure row)) madeEdge 0 ?_ ?_ (.refl _ _)
    · change SourceEqualityNativeDemandHeapPrimitives.WorkInputs afterMu.native.machine.heap
        (makeEdge row.entry.key.symbol top [first,mu])
      rw [after_mu_heap]
      apply SourceEqualityNativeDemandHeapPrimitives.WorkInputs.edge
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact first_available
      · rcases List.mem_cons.mp member with rfl | member
        · exact mu_available
        · cases member
    · cbv
  have built : Trace 5 (.code (SourceEqualityNativeCheckedCode.children domain row row allocated)) checkedEdge
      (.code (.pure row)) madeEdge := by
    have joined := (walked.trace.bind (fun values => .work (makeEdge row.entry.key.symbol top values) .pure)).trans made
    have shape : SourceEqualityNativeCheckedCode.children domain row row allocated =
        (SourceRecursiveIntersectionCode.walk (fun pair : Node × Node => requestNode domain pair.1 pair.2)
          [(first,first),(mu,mu)]).bind (fun values => .work (makeEdge row.entry.key.symbol top values) .pure) := by
      unfold SourceEqualityNativeCheckedCode.children
      rw [row_children]
      rfl
    rw [shape]
    exact joined
  have bodyTrace : Trace 6 (.edgeBody request .pure) edgeStarted (.code (.pure row)) madeEdge :=
    .cons _ _ _ _ _ _ _ trivial bodyStep built
  have finish : Trace 1 (.code (.finishEdge 0 row (.pure row))) madeEdge (.code (.pure row)) edgeAfter := by
    refine Trace.cons (.code (.finishEdge 0 row (.pure row))) madeEdge (.code (.pure row)) edgeAfter (.code (.pure row)) edgeAfter 0 ?_ rfl (.refl _ _)
    refine ⟨request,by cbv,?_⟩
    rw [made_edge_heap]
    exact row_resident
  have tail := (bodyTrace.bind (fun value => .finishEdge 0 value (.pure value))).trans finish
  exact .cons _ _ _ _ _ _ _ ⟨edge_ready,by cbv⟩ one tail
private theorem warm_edge : Trace 1 (.code (requestEdge domain row row)) edgeAfter (.code (.pure row)) edgeAfter := by
  refine Trace.cons (.code (requestEdge domain row row)) edgeAfter (.code (.pure row)) edgeAfter (.code (.pure row)) edgeAfter 0 ?_ ?_ (.refl _ _)
  · refine ⟨?_,by cbv⟩
    rw [edge_after_machine]
    exact edge_ready
  · cbv


private def interposedRow := (run (makeEdge ("interposed",.top) top []) heap).1
private def interposedHeap := (run (makeEdge ("interposed",.top) top []) heap).2
private def advanced : Checked 8 := SourceCurrentAllocatedQueryMemo.advancePhysical edgeAfter ⟨interposedHeap,checkedOps⟩
private theorem interposed : Trace 1 (.code (.work (makeEdge ("interposed",.top) top []) .pure)) edgeAfter
    (.code (.pure interposedRow)) advanced := by
  refine Trace.cons (.code (.work (makeEdge ("interposed",.top) top []) .pure)) edgeAfter
    (.code (.pure interposedRow)) advanced (.code (.pure interposedRow)) advanced 0 ?_ ?_ (.refl _ _)
  · exact SourceEqualityNativeDemandHeapPrimitives.WorkInputs.edge _ _ [] (by intro value member; cases member)
  · cbv
private theorem cold_good : Good edgeAfter :=
  (SourceCurrentAllocatedNativeSemanticTraceReadback.effects cold_edge initial_good (by intro value; trivial)).1
private theorem advance_good : Good advanced := by
  have loaded : SourceCurrentConjunctionEquality.FieldAvailable edgeAfter.operations top := by
    have old := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
      SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid
    have growth := (SourceCurrentAllocatedNativeSemanticTraceReadback.effects cold_edge initial_good (by intro value; trivial)).2.2.2.1
    exact old.2.2.grows growth
  have fields : SourceCurrentAllocatedNativeFieldClosure.Fields
      (.code (.work (makeEdge ("interposed",.top) top []) .pure)) edgeAfter :=
    ⟨SourceCurrentAllocatedNativeCodeFields.makeEdge_fields _ _ _ _ loaded,fun _ => trivial⟩
  exact (SourceCurrentAllocatedNativeSemanticTraceReadback.effects interposed cold_good fields).1
private theorem warm_after_advance : Trace 1 (.code (requestEdge domain row row)) advanced (.code (.pure row)) advanced := by
  refine Trace.cons (.code (requestEdge domain row row)) advanced (.code (.pure row)) advanced (.code (.pure row)) advanced 0 ?_ ?_ (.refl _ _)
  · have present : advanced.native.edges.cells 0 = some ⟨request,.returned row⟩ := by cbv
    have ready : EdgeReady advanced.native.machine request := (advance_good.native.edges.checked 0 _ present).1
    exact ⟨ready,by cbv⟩
  · cbv


private theorem advanced_history : SourceCurrentNativeEdgeWriterGrowth.History advanced := by
  have started : SourceCurrentNativeEdgeWriterGrowth.History before := .initial machine operations
  have first := SourceCurrentNativeEdgeWriterGrowth.History.trace started _ 8 row
    (by intro value; trivial) initial_good (by intro value; trivial) cold_edge
  have loaded : SourceCurrentConjunctionEquality.FieldAvailable edgeAfter.operations top := by
    have old := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
      SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid
    exact old.2.2.grows (SourceCurrentAllocatedNativeSemanticTraceReadback.effects cold_edge initial_good
      (by intro value; trivial)).2.2.2.1
  have fields : SourceCurrentAllocatedNativeFieldClosure.Fields
      (.code (.work (makeEdge ("interposed",.top) top []) .pure)) edgeAfter :=
    ⟨SourceCurrentAllocatedNativeCodeFields.makeEdge_fields _ _ _ _ loaded,fun _ => trivial⟩
  have growth := (SourceCurrentAllocatedNativeSemanticTraceReadback.effects interposed cold_good fields).2.2.1.growth
  exact first.advance ⟨interposedHeap,checkedOps⟩ growth

private def other : Node := (run (makeNode [row,interposedRow]) interposedHeap).1
private def otherHeap := (run (makeNode [row,interposedRow]) interposedHeap).2
private def otherAfter : Checked 8 := SourceCurrentAllocatedQueryMemo.advancePhysical advanced ⟨otherHeap,checkedOps⟩
private theorem other_edges : ∀ edge ∈ [row,interposedRow], EdgeResident advanced.native.machine.heap edge := by
  intro edge member
  rcases List.mem_cons.mp member with rfl | member
  · cbv
  · rcases List.mem_cons.mp member with rfl | member
    · cbv
    · cases member
private theorem other_inputs : SourceEqualityNativeDemandHeapPrimitives.WorkInputs advanced.native.machine.heap
    (makeNode [row,interposedRow]) := .node _ other_edges
private theorem other_fields : SourceCurrentAllocatedNativeFieldClosure.Fields
    (.code (.work (makeNode [row,interposedRow]) .pure)) advanced :=
  ⟨SourceCurrentAllocatedNativeCodeFields.makeNode_fields advanced.operations [row,interposedRow],fun _ => trivial⟩
private theorem make_other : Trace 1 (.code (.work (makeNode [row,interposedRow]) .pure)) advanced
    (.code (.pure other)) otherAfter := by
  refine Trace.cons _ _ _ _ _ _ _ other_inputs ?_ (.refl _ _)
  rfl
private theorem other_good : Good otherAfter :=
  (SourceCurrentAllocatedNativeSemanticTraceReadback.effects make_other advance_good
    other_fields).1
private theorem other_history : SourceCurrentNativeEdgeWriterGrowth.History otherAfter :=
  SourceCurrentNativeEdgeWriterGrowth.History.trace advanced_history _ 1 other
    (by intro value; trivial) advance_good
    other_fields make_other
private theorem other_available : Available otherAfter.native.machine.heap other := by
  exact (SourceEqualityNativeDemandHeapPrimitives.node [row,interposedRow] advanced.native.machine.heap
    advance_good.heap other_edges).2
private theorem root_available : Available otherAfter.native.machine.heap root := by
  have original := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  have firstKeeps := (SourceCurrentAllocatedNativeSemanticTraceReadback.effects cold_edge initial_good
    (by intro value; trivial)).2.2.1
  have interposedFields : SourceCurrentAllocatedNativeFieldClosure.Fields
      (.code (.work (makeEdge ("interposed",.top) top []) .pure)) edgeAfter := by
    have old := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
      SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid
    exact ⟨SourceCurrentAllocatedNativeCodeFields.makeEdge_fields _ _ _ _
      (old.2.2.grows (SourceCurrentAllocatedNativeSemanticTraceReadback.effects cold_edge initial_good
        (by intro value; trivial)).2.2.2.1),fun _ => trivial⟩
  have secondKeeps := (SourceCurrentAllocatedNativeSemanticTraceReadback.effects interposed cold_good interposedFields).2.2.1
  have thirdKeeps := (SourceCurrentAllocatedNativeSemanticTraceReadback.effects make_other advance_good other_fields).2.2.1
  exact thirdKeeps.available root (secondKeeps.available root (firstKeeps.available root original))
private def rootRequest : NodeRequest Symbol Guard := ⟨domain,root,other⟩
private def rootChosen := (lookupNode 8 rootRequest otherAfter.native).2
private def rootRunning := (demandNode 2 rootChosen).2
private def rootStarted : Checked 8 := ⟨rootRunning,checkedOps⟩
private theorem root_ready : NodeReady otherAfter.native.machine rootRequest :=
  ⟨empty_domain _,root_available,other_available⟩
private theorem root_safe : SourceRecursiveIntersectionMemo.KeySafe 8 domain root other := by
  unfold SourceRecursiveIntersectionMemo.KeySafe
  refine ⟨by decide,by cbv,.node 5,.node 6,?_,?_,?_,?_⟩ <;> cbv
private theorem root_start_step : step (.code (requestNode domain root other)) otherAfter =
    .yielded (.code ((compileNode rootRequest).bind (fun value => .finishNode 2 value (.pure value)))) rootStarted := by cbv
private theorem root_start_good : Good rootStarted := by
  have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants
    (.code (requestNode domain root other)) otherAfter other_good
    ⟨root_ready,by intro key found; exact root_safe⟩ (by intro value; trivial)
  simpa only [root_start_step,Outcome.state] using checked.1
private theorem root_owner : rootStarted.native.nodes.cells 2 = some ⟨rootRequest,.evaluating⟩ := by cbv
private theorem root_rows : compileNode rootRequest = compileRows domain (nodeEdges root) (nodeEdges other) := by cbv
private theorem root_pair : pairs (nodeEdges root) (nodeEdges other) = [(row,row)] := by cbv
private theorem warm_at_owner : Trace 1 (.code (requestEdge domain row row)) rootStarted (.code (.pure row)) rootStarted := by
  refine Trace.cons _ _ _ _ _ _ _ ?_ ?_ (.refl _ _)
  · have present : rootStarted.native.edges.cells 0 = some ⟨request,.returned row⟩ := by cbv
    exact ⟨(root_start_good.native.edges.checked 0 _ present).1,by cbv⟩
  · cbv
private theorem make_root : Trace 1 (.code (.work (makeNode [row]) .pure)) rootStarted
    (.code (.pure root)) rootStarted := by
  refine Trace.cons _ _ _ _ _ _ _ ?_ ?_ (.refl _ _)
  · apply SourceEqualityNativeDemandHeapPrimitives.WorkInputs.node
    intro edge member
    rcases List.mem_cons.mp member with rfl | member
    · cbv
    · cases member
  · cbv
private theorem root_body : Trace 2 (.code (compileRows domain (nodeEdges root) (nodeEdges other))) rootStarted
    (.code (.pure root)) rootStarted := by
  have walked : SourceCurrentAllocatedNativeSemanticTraceReadback.Walk
      (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
      [(row,row)] rootStarted [row] rootStarted 1 :=
    .cons (row,row) [] rootStarted rootStarted rootStarted row [] 1 0 warm_at_owner (.nil _)
  have joined := (walked.trace.bind (fun values => .work (makeNode values) .pure)).trans make_root
  simpa only [compileRows,root_pair,Control.bind] using joined
private def rootAfter : Checked 8 := ⟨finishNode 2 root rootStarted.native,checkedOps⟩
private theorem root_finish : Trace 1 (.code (.finishNode 2 root (.pure root))) rootStarted
    (.code (.pure root)) rootAfter := by
  refine Trace.cons _ _ _ _ _ _ _ ⟨rootRequest,root_owner,?_⟩ rfl (.refl _ _)
  have same : rootStarted.native.machine.heap = otherAfter.native.machine.heap := by cbv
  rw [same]
  exact root_available
private theorem root_call : Trace 4 (.code (requestNode domain root other)) otherAfter
    (.code (.pure root)) rootAfter := by
  have body : Trace 2 (.code (compileNode rootRequest)) rootStarted (.code (.pure root)) rootStarted := by
    rw [root_rows]
    exact root_body
  exact .cons _ _ _ _ _ _ _ ⟨root_ready,by intro key found; exact root_safe⟩ root_start_step
    ((body.bind (fun value => .finishNode 2 value (.pure value))).trans root_finish)
private theorem root_history : SourceCurrentNativeEdgeWriterGrowth.History rootAfter :=
  other_history.query rootRequest 4 root other_good root_call
private theorem retained : SourceEqualityNativeDemandMemo.Retained rootStarted.native rootAfter.native :=
  SourceCurrentNativeWriterReadyRetention.trace_retained root_finish root_start_good.native.shape

private theorem witness :
    built = .done root heap ∧
    Good rootStarted ∧
    rootStarted.native.nodes.cells 2 = some ⟨rootRequest,.evaluating⟩ ∧
    Trace 2 (.code (compileRows domain (nodeEdges root) (nodeEdges other))) rootStarted (.code (.pure root)) rootStarted ∧
    Trace 4 (.code (requestNode domain root other)) otherAfter (.code (.pure root)) rootAfter ∧
    SourceCurrentNativeEdgeWriterGrowth.History rootAfter ∧
    rootStarted.native.edges.cells 0 = some ⟨request,.returned row⟩ ∧
    row.children = [first,mu] ∧
    (∃ (leftIndex rightIndex : Nat) (leftRow rightRow : EdgeValue Symbol Guard) (handle : Nat)
       (leftChild rightChild : Node) (callBefore callAfter : Checked 8) (childFuel : Nat),
      (nodeEdges root)[leftIndex]? = some leftRow ∧ (nodeEdges other)[rightIndex]? = some rightRow ∧
      leftRow.entry.key.symbol = rightRow.entry.key.symbol ∧
      SourceCurrentNativeEdgeWriterGrowth.Written (width := 8) handle ⟨domain,leftRow,rightRow⟩ row rootAfter.native.machine.heap ∧
      row.entry.key.symbol = leftRow.entry.key.symbol ∧
      row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin leftRow.entry.key.constraint rightRow.entry.key.constraint ∧
      leftRow.children[1]? = some leftChild ∧ rightRow.children[1]? = some rightChild ∧
      Good callBefore ∧ Good callAfter ∧
      Grows callBefore.native.machine.heap rootAfter.native.machine.heap ∧
      Grows callAfter.native.machine.heap rootAfter.native.machine.heap ∧
      Trace childFuel (.code (requestNode domain leftChild rightChild)) callBefore (.code (.pure mu)) callAfter) := by
  refine ⟨constructed,root_start_good,root_owner,root_body,root_call,root_history,by cbv,row_children,?_⟩
  exact SourceCurrentNativeReaderRowLineage.rows_child root_history domain (nodeEdges root) (nodeEdges other)
    2 root root_start_good root_body retained 0 row (by cbv) 1 mu (by cbv)

/-- A real active ordinary owner reuses an earlier edge and recovers its historical ordered Mu child call. -/
theorem active_owner_reads_earlier_edge :
    built = .done root heap ∧
    Good rootStarted ∧
    rootStarted.native.nodes.cells 2 = some ⟨rootRequest,.evaluating⟩ ∧
    Trace 2 (.code (compileRows domain (nodeEdges root) (nodeEdges other))) rootStarted (.code (.pure root)) rootStarted ∧
    Trace 4 (.code (requestNode domain root other)) otherAfter (.code (.pure root)) rootAfter ∧
    SourceCurrentNativeEdgeWriterGrowth.History rootAfter ∧
    rootStarted.native.edges.cells 0 = some ⟨request,.returned row⟩ ∧
    row.children = [first,mu] ∧
    (∃ (leftIndex rightIndex : Nat) (leftRow rightRow : EdgeValue Symbol Guard) (handle : Nat)
       (leftChild rightChild : Node) (callBefore callAfter : Checked 8) (childFuel : Nat),
      (nodeEdges root)[leftIndex]? = some leftRow ∧ (nodeEdges other)[rightIndex]? = some rightRow ∧
      leftRow.entry.key.symbol = rightRow.entry.key.symbol ∧
      SourceCurrentNativeEdgeWriterGrowth.Written (width := 8) handle ⟨domain,leftRow,rightRow⟩ row rootAfter.native.machine.heap ∧
      row.entry.key.symbol = leftRow.entry.key.symbol ∧
      row.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin leftRow.entry.key.constraint rightRow.entry.key.constraint ∧
      leftRow.children[1]? = some leftChild ∧ rightRow.children[1]? = some rightChild ∧
      Good callBefore ∧ Good callAfter ∧
      Grows callBefore.native.machine.heap rootAfter.native.machine.heap ∧
      Grows callAfter.native.machine.heap rootAfter.native.machine.heap ∧
      Trace childFuel (.code (requestNode domain leftChild rightChild)) callBefore (.code (.pure mu)) callAfter) := witness
end MicroCFTA.ReaderRowLineageIntegration
