import MicroCFTA.SourceCurrentNativeForwardLineage
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
namespace MicroCFTA.NativeForwardKernels
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

private theorem advanced_root_available : Available advanced.native.machine.heap root :=
  InternedProbeProvenance.available_after_run (makeEdge (("interposed",.top) : Symbol) top []) heap
    initial_good.heap.semantic.1.normal.facts.coherent.valid
    ((InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed)
private theorem advanced_row : EdgeResident advanced.native.machine.heap row := by
  have present : advanced.native.edges.cells 0 = some ⟨request,.returned row⟩ := by cbv
  exact (advance_good.native.edges.checked 0 _ present).2
private theorem advanced_extra : EdgeResident advanced.native.machine.heap interposedRow :=
  (InternedNestedFacts.edge_verified ("interposed",.top) top [] heap initial_good.heap.semantic.1.normal.facts
    (by intro value member; cases member)).result interposedRow interposedHeap rfl
private theorem wide_rows : ∀ edge ∈ [row,interposedRow], EdgeResident advanced.native.machine.heap edge := by
  intro edge member
  rcases List.mem_cons.mp member with rfl | member
  · exact advanced_row
  · rcases List.mem_cons.mp member with rfl | member
    · exact advanced_extra
    · cases member
private def wide := (run (makeNode [row,interposedRow]) advanced.native.machine.heap).1
private def wideState : Checked 8 := SourceCurrentAllocatedQueryMemo.advancePhysical advanced
  ⟨(run (makeNode [row,interposedRow]) advanced.native.machine.heap).2,checkedOps⟩
private theorem wide_work : Trace 1 (.code (.work (makeNode [row,interposedRow]) .pure)) advanced
    (.code (.pure wide)) wideState := by
  refine Trace.cons (.code (.work (makeNode [row,interposedRow]) .pure)) advanced
    (.code (.pure wide)) wideState (.code (.pure wide)) wideState 0 ?_ ?_ (.refl _ _)
  · exact SourceEqualityNativeDemandHeapPrimitives.WorkInputs.node _ wide_rows
  · cbv
private theorem wide_fields : SourceCurrentAllocatedNativeFieldClosure.Fields
    (.code (.work (makeNode [row,interposedRow]) .pure)) advanced :=
  ⟨SourceCurrentAllocatedNativeCodeFields.makeNode_fields _ _,fun _ => trivial⟩
private theorem wide_good : Good wideState :=
  (SourceCurrentAllocatedNativeSemanticTraceReadback.effects wide_work advance_good wide_fields).1
private theorem wide_history : SourceCurrentNativeEdgeWriterGrowth.History wideState :=
  SourceCurrentNativeEdgeWriterGrowth.History.trace advanced_history _ 1 wide
    (by intro value; trivial) advance_good wide_fields wide_work
private theorem wide_available : Available wideState.native.machine.heap wide :=
  (InternedNestedFacts.node_verified [row,interposedRow] advanced.native.machine.heap
    advance_good.heap.semantic.1.normal.facts wide_rows).result wide wideState.native.machine.heap rfl
private theorem root_at_wide : Available wideState.native.machine.heap root :=
  InternedProbeProvenance.available_after_run (makeNode [row,interposedRow]) advanced.native.machine.heap
    advance_good.heap.semantic.1.normal.facts.coherent.valid advanced_root_available
private def nodeRequest : NodeRequest Symbol Guard := ⟨domain,root,wide⟩
private theorem node_ready : NodeReady wideState.native.machine nodeRequest :=
  ⟨empty_domain _,root_at_wide,wide_available⟩
private theorem node_safe : SourceRecursiveIntersectionMemo.KeySafe 8 domain root wide := by
  unfold SourceRecursiveIntersectionMemo.KeySafe
  refine ⟨by decide,by cbv,.node 5,.node 6,?_,?_,?_,?_⟩ <;> cbv
private def chosenNode := (lookupNode 8 nodeRequest wideState.native).2
private def runningNode := (demandNode 2 chosenNode).2
private def nodeStarted : Checked 8 := ⟨runningNode,checkedOps⟩
private def nodeAfter : Checked 8 := ⟨finishNode 2 root runningNode,checkedOps⟩
private theorem node_step : step (.code (requestNode domain root wide)) wideState = .yielded
    (.code ((compileNode nodeRequest).bind (fun value => .finishNode 2 value (.pure value)))) nodeStarted := by cbv
private theorem started_good : Good nodeStarted := by
  have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants
    (.code (requestNode domain root wide)) wideState wide_good
    ⟨node_ready,by intro key found; exact node_safe⟩ (by intro value; trivial)
  simpa only [node_step,Outcome.state] using checked.1
private theorem warm_row : Trace 1 (.code (requestEdge domain row row)) nodeStarted (.code (.pure row)) nodeStarted := by
  refine Trace.cons (.code (requestEdge domain row row)) nodeStarted (.code (.pure row)) nodeStarted
    (.code (.pure row)) nodeStarted 0 ?_ ?_ (.refl _ _)
  · have present : nodeStarted.native.edges.cells 0 = some ⟨request,.returned row⟩ := by cbv
    exact ⟨(started_good.native.edges.checked 0 _ present).1,by cbv⟩
  · cbv
private theorem root_made : Trace 1 (.code (.work (makeNode [row]) .pure)) nodeStarted
    (.code (.pure root)) nodeStarted := by
  refine Trace.cons (.code (.work (makeNode [row]) .pure)) nodeStarted (.code (.pure root)) nodeStarted
    (.code (.pure root)) nodeStarted 0 ?_ ?_ (.refl _ _)
  · apply SourceEqualityNativeDemandHeapPrimitives.WorkInputs.node
    intro edge member
    have same := List.mem_singleton.mp member
    subst edge
    exact (started_good.native.edges.checked 0 _ (by cbv : nodeStarted.native.edges.cells 0 = some ⟨request,.returned row⟩)).2
  · cbv
private theorem node_body : Trace 2 (.code (compileNode nodeRequest)) nodeStarted (.code (.pure root)) nodeStarted := by
  have walked : SourceCurrentAllocatedNativeSemanticTraceReadback.Walk
      (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
      [(row,row)] nodeStarted [row] nodeStarted 1 :=
    .cons (row,row) [] nodeStarted nodeStarted nodeStarted row [] 1 0 warm_row (.nil _)
  have compiled : compileNode nodeRequest =
      (SourceRecursiveIntersectionCode.walk
        (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
        [(row,row)]).bind (fun values => .work (makeNode values) .pure) := by cbv
  rw [compiled]
  exact (walked.trace.bind (fun values => .work (makeNode values) .pure)).trans root_made
private theorem node_finish : Trace 1 (.code (.finishNode 2 root (.pure root))) nodeStarted
    (.code (.pure root)) nodeAfter := by
  refine Trace.cons (.code (.finishNode 2 root (.pure root))) nodeStarted (.code (.pure root)) nodeAfter
    (.code (.pure root)) nodeAfter 0 ?_ rfl (.refl _ _)
  refine ⟨nodeRequest,by cbv,?_⟩
  rw [show nodeStarted.native.machine.heap = wideState.native.machine.heap by cbv]
  exact root_at_wide
private theorem node_call : Trace 4 (.code (requestNode domain root wide)) wideState (.code (.pure root)) nodeAfter := by
  have tail := (node_body.bind (fun value => .finishNode 2 value (.pure value))).trans node_finish
  exact .cons _ _ _ _ _ _ _ ⟨node_ready,by intro key found; exact node_safe⟩ node_step tail
private theorem final_history : SourceCurrentNativeEdgeWriterGrowth.History nodeAfter :=
  wide_history.query nodeRequest 4 root wide_good node_call
private theorem final_good : Good nodeAfter :=
  (SourceCurrentAllocatedNativeSemanticTraceReadback.effects node_call wide_good (by intro value; trivial)).1
private def entry (value : Node) : Interned InternedBinderProtocol.NodeKey :=
  match value with
  | .node entry .. => entry
  | _ => {key := .node [],identity := 0}
private def level : Node → Nat | .node _ _ depth _ => depth | _ => 0
private theorem root_shape : root = .node (entry root) [row] (level root) [] := by cbv
private theorem wide_shape : wide = .node (entry wide) [row,interposedRow] (level wide) [] := by cbv
private theorem ordinary_branch : SourceRecursiveIntersectionControl.decision nodeRequest.domain.key
    nodeRequest.left nodeRequest.right = .ordinary := by cbv
private theorem row_selected : (nodeEdges root)[0]? = some row := by cbv
private theorem first_selected : row.children[0]? = some first := by cbv
private theorem mu_selected : row.children[1]? = some mu := by cbv
private theorem node_stored : nodeAfter.native.nodes.cells 2 = some ⟨nodeRequest,.returned root⟩ := by cbv
private def reverseRequest : NodeRequest Symbol Guard := ⟨domain,wide,root⟩
private theorem reverse_ready : NodeReady nodeAfter.native.machine reverseRequest := by
  have ready := (final_good.native.nodes.checked 2 _ node_stored).1
  exact ⟨ready.1,ready.2.2,ready.2.1⟩
private theorem reverse_safe : SourceRecursiveIntersectionMemo.KeySafe 8 domain wide root := node_safe.swap
private def reverseChosen := (lookupNode 8 reverseRequest nodeAfter.native).2
private def reverseRunning := (demandNode 3 reverseChosen).2
private def reverseStarted : Checked 8 := ⟨reverseRunning,checkedOps⟩
private def reverseAfter : Checked 8 := ⟨finishNode 3 root reverseRunning,checkedOps⟩
private theorem reverse_step : step (.code (requestNode domain wide root)) nodeAfter = .yielded
    (.code ((compileNode reverseRequest).bind (fun value => .finishNode 3 value (.pure value)))) reverseStarted := by cbv
private theorem reverse_good : Good reverseStarted := by
  have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants
    (.code (requestNode domain wide root)) nodeAfter final_good
    ⟨reverse_ready,by intro key found; exact reverse_safe⟩ (by intro value; trivial)
  simpa only [reverse_step,Outcome.state] using checked.1
private theorem forward_cell : reverseStarted.native.nodes.cells 2 = some ⟨nodeRequest,.returned root⟩ := by cbv
private theorem forwarded_call : Trace 1 (.code (requestNode domain root wide)) reverseStarted
    (.code (.pure root)) reverseStarted := by
  refine Trace.cons (.code (requestNode domain root wide)) reverseStarted (.code (.pure root)) reverseStarted
    (.code (.pure root)) reverseStarted 0 ⟨(reverse_good.native.nodes.checked 2 _ forward_cell).1,
      by intro key found; exact node_safe⟩ (by cbv) (.refl _ _)
private theorem reverse_body : Trace 1 (.code (compileNode reverseRequest)) reverseStarted
    (.code (.pure root)) reverseStarted := by
  have compiled : compileNode reverseRequest = requestNode domain root wide := by cbv
  rw [compiled]
  exact forwarded_call
private theorem reverse_finish : Trace 1 (.code (.finishNode 3 root (.pure root))) reverseStarted
    (.code (.pure root)) reverseAfter := by
  refine Trace.cons (.code (.finishNode 3 root (.pure root))) reverseStarted (.code (.pure root)) reverseAfter
    (.code (.pure root)) reverseAfter 0 ⟨reverseRequest,by cbv,(reverse_good.native.nodes.checked 2 _ forward_cell).2⟩
    rfl (.refl _ _)
private theorem reverse_call : Trace 3 (.code (requestNode domain wide root)) nodeAfter
    (.code (.pure root)) reverseAfter := by
  exact .cons _ _ _ _ _ _ _ ⟨reverse_ready,by intro key found; exact reverse_safe⟩ reverse_step
    ((reverse_body.bind (fun value => .finishNode 3 value (.pure value))).trans reverse_finish)
private theorem reverse_history : SourceCurrentNativeEdgeWriterGrowth.History reverseAfter :=
  final_history.query reverseRequest 3 root final_good reverse_call
private theorem reverse_stored : reverseAfter.native.nodes.cells 3 = some ⟨reverseRequest,.returned root⟩ := by cbv
private theorem swap_branch : SourceRecursiveIntersectionControl.decision reverseRequest.domain.key
    reverseRequest.left reverseRequest.right = .swap := by cbv
private theorem self_branch : SourceRecursiveIntersectionControl.decision domain.key first first = .self := by cbv

private theorem captured_swap :
    ∃ (before after : Checked 8) (fuel : Nat),
      before.native.nodes.cells 3 = some ⟨reverseRequest,.evaluating⟩ ∧
      Trace fuel (.code (compileNode reverseRequest)) before (.code (.pure root)) after ∧
      after.native.nodes.cells 3 = some ⟨reverseRequest,.evaluating⟩ ∧
      Trace 1 (.code (.finishNode 3 root (.pure root))) after (.code (.pure root))
        {after with native := finishNode 3 root after.native} ∧
      SourceCurrentNativeForwardLineage.Forwarded reverseAfter nodeRequest before after root := by
  obtain ⟨before,after,fuel,_,_,owner,body,ownerKept,finish,_,_,_,branch⟩ :=
    SourceCurrentNativeForwardLineage.writer reverse_history 3 reverseRequest root reverse_stored (Or.inl swap_branch)
  rcases branch with ⟨_,forwarded⟩ | ⟨wrong,_⟩ | ⟨wrong,_⟩
  · exact ⟨before,after,fuel,owner,body,ownerKept,finish,forwarded⟩
  · rw [swap_branch] at wrong; cases wrong
  · rw [swap_branch] at wrong; cases wrong
private theorem captured_self :
    ∃ (before after : Checked 8) (fuel : Nat),
      Trace fuel (.code (compileNode (⟨domain,first,first⟩ : NodeRequest Symbol Guard)))
        before (.code (.pure first)) after ∧ fuel = 0 ∧ after = before := by
  have stored : reverseAfter.native.nodes.cells 0 = some ⟨⟨domain,first,first⟩,.returned first⟩ := by cbv
  obtain ⟨before,after,fuel,_,_,_,body,_,_,_,_,_,branch⟩ :=
    SourceCurrentNativeForwardLineage.writer reverse_history 0 ⟨domain,first,first⟩ first stored (Or.inr (Or.inr self_branch))
  rcases branch with ⟨wrong,_⟩ | ⟨wrong,_⟩ | ⟨_,empty,_,unchanged⟩
  · rw [self_branch] at wrong; cases wrong
  · rw [self_branch] at wrong; cases wrong
  · exact ⟨before,after,fuel,body,empty,unchanged⟩
private theorem actual_witness :
    Trace 3 (.code (requestNode domain wide root)) nodeAfter (.code (.pure root)) reverseAfter ∧
    SourceCurrentNativeForwardLineage.Forwarded reverseAfter nodeRequest reverseStarted reverseStarted root ∧
    (∃ (before after : Checked 8) (fuel : Nat),
      before.native.nodes.cells 3 = some ⟨reverseRequest,.evaluating⟩ ∧
      Trace fuel (.code (compileNode reverseRequest)) before (.code (.pure root)) after ∧
      after.native.nodes.cells 3 = some ⟨reverseRequest,.evaluating⟩ ∧
      Trace 1 (.code (.finishNode 3 root (.pure root))) after (.code (.pure root))
        {after with native := finishNode 3 root after.native} ∧
      SourceCurrentNativeForwardLineage.Forwarded reverseAfter nodeRequest before after root) ∧
    (∃ (before after : Checked 8) (fuel : Nat),
      Trace fuel (.code (compileNode (⟨domain,first,first⟩ : NodeRequest Symbol Guard)))
        before (.code (.pure first)) after ∧ fuel = 0 ∧ after = before) := by
  have retained := SourceCurrentNativeWriterReadyRetention.trace_retained reverse_finish reverse_good.native.shape
  have forwarded := SourceCurrentNativeForwardLineage.swap reverse_history reverseRequest 1 root
    reverse_good reverse_body retained swap_branch
  exact ⟨reverse_call,forwarded,captured_swap,captured_self⟩

/-- Own cold and warm ordinary history supplies a real swap forwarding hit and a captured literal self body. -/
theorem constructed_swap_self :
    Trace 3 (.code (requestNode domain wide root)) nodeAfter (.code (.pure root)) reverseAfter ∧
    SourceCurrentNativeForwardLineage.Forwarded reverseAfter nodeRequest reverseStarted reverseStarted root ∧
    (∃ (before after : Checked 8) (fuel : Nat),
      before.native.nodes.cells 3 = some ⟨reverseRequest,.evaluating⟩ ∧
      Trace fuel (.code (compileNode reverseRequest)) before (.code (.pure root)) after ∧
      after.native.nodes.cells 3 = some ⟨reverseRequest,.evaluating⟩ ∧
      Trace 1 (.code (.finishNode 3 root (.pure root))) after (.code (.pure root))
        {after with native := finishNode 3 root after.native} ∧
      SourceCurrentNativeForwardLineage.Forwarded reverseAfter nodeRequest before after root) ∧
    (∃ (before after : Checked 8) (fuel : Nat),
      Trace fuel (.code (compileNode (⟨domain,first,first⟩ : NodeRequest Symbol Guard)))
        before (.code (.pure first)) after ∧ fuel = 0 ∧ after = before) := actual_witness
end MicroCFTA.NativeForwardKernels

#check @MicroCFTA.NativeForwardKernels.constructed_swap_self
#print MicroCFTA.NativeForwardKernels.constructed_swap_self
#print axioms MicroCFTA.NativeForwardKernels.constructed_swap_self
