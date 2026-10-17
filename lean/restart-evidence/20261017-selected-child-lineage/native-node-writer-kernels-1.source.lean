import MicroCFTA.SourceCurrentNativeNodeWriterHistory
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
namespace MicroCFTA.NativeNodeWriterKernels
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

private theorem row_live : Value.empty ∉ row.children := by
  rw [show row.children = [first,mu] by cbv]
  intro member
  rcases List.mem_cons.mp member with bad | member
  · have impossible : first ≠ Value.empty := by
      intro same
      have ref := congrArg Value.referenceOf same
      cbv at ref
      cases ref
    exact impossible bad.symm
  · rcases List.mem_cons.mp member with bad | member
    · have impossible : mu ≠ Value.empty := by
        intro same
        have ref := congrArg Value.referenceOf same
        cbv at ref
        cases ref
      exact impossible bad.symm
    · cases member
private theorem actual_node_witness :
    Good advanced ∧
    SourceCurrentNativeNodeWriterHistory.Written (width := 8) 0 ⟨domain,first,first⟩ first advanced.native.machine.heap ∧
    SourceCurrentNativeNodeWriterHistory.Written (width := 8) 1 ⟨domain,mu,mu⟩ mu advanced.native.machine.heap ∧
    Trace 1 (.code (requestNode domain first first)) advanced (.code (.pure first)) advanced ∧
    Trace 1 (.code (requestNode domain mu mu)) advanced (.code (.pure mu)) advanced ∧
    heap.edges.next < advanced.native.machine.heap.edges.next := by
  have firstStored : advanced.native.nodes.cells 0 = some ⟨⟨domain,first,first⟩,.returned first⟩ := by cbv
  have muStored : advanced.native.nodes.cells 1 = some ⟨⟨domain,mu,mu⟩,.returned mu⟩ := by cbv
  have firstReady := (advance_good.native.nodes.checked 0 _ firstStored).1
  have muReady := (advance_good.native.nodes.checked 1 _ muStored).1
  have firstWritten := SourceCurrentNativeNodeWriterHistory.warm advanced_history advance_good
    ⟨domain,first,first⟩ advanced.native advanced.native 0 first firstReady first_safe (by cbv) (by cbv)
  have muWritten := SourceCurrentNativeNodeWriterHistory.warm advanced_history advance_good
    ⟨domain,mu,mu⟩ advanced.native advanced.native 1 mu muReady mu_safe (by cbv) (by cbv)
  refine ⟨advance_good,firstWritten,muWritten,?_,?_,?_⟩
  · refine Trace.cons (.code (requestNode domain first first)) advanced (.code (.pure first)) advanced
      (.code (.pure first)) advanced 0 ⟨firstReady,by intro key found; exact first_safe⟩ ?_ (.refl _ _)
    cbv
  · refine Trace.cons (.code (requestNode domain mu mu)) advanced (.code (.pure mu)) advanced
      (.code (.pure mu)) advanced 0 ⟨muReady,by intro key found; exact mu_safe⟩ ?_ (.refl _ _)
    cbv
  · cbv

/-- Own cold checked calls retain ordinary and productive-Mu node writers through allocation and exact warm demands. -/
theorem actual_node_writers :
    Good advanced ∧
    SourceCurrentNativeNodeWriterHistory.Written (width := 8) 0 ⟨domain,first,first⟩ first advanced.native.machine.heap ∧
    SourceCurrentNativeNodeWriterHistory.Written (width := 8) 1 ⟨domain,mu,mu⟩ mu advanced.native.machine.heap ∧
    Trace 1 (.code (requestNode domain first first)) advanced (.code (.pure first)) advanced ∧
    Trace 1 (.code (requestNode domain mu mu)) advanced (.code (.pure mu)) advanced ∧
    heap.edges.next < advanced.native.machine.heap.edges.next := actual_node_witness
end MicroCFTA.NativeNodeWriterKernels

#check @MicroCFTA.NativeNodeWriterKernels.actual_node_writers
#print MicroCFTA.NativeNodeWriterKernels.actual_node_writers
#print axioms MicroCFTA.NativeNodeWriterKernels.actual_node_writers
