import MicroCFTA.SourceCurrentNativeEdgeWriterGrowth
import MicroCFTA.SourceEqualityNativeDemandMismatchProvenance
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.SourceEqualityAnnotationConstruction
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
noncomputable section
namespace MicroCFTA.NativeEdgeWriterGrowthKernels
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
private def row : EdgeValue Symbol Guard := match first with
  | .node _ (edge :: _) _ _ => edge
  | _ => (run (makeEdge ("fallback",.top) top []) empty).1
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
private theorem row_resident : EdgeResident heap row := by
  have original := ((InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed).children first (by cbv; exact .head _)
  exact resident_edges heap initial_good.heap.semantic.1.normal.facts.linked first original.resident row (by cbv; exact .head _)
private theorem edge_ready : EdgeReady machine request := ⟨empty_domain machine,row_resident,row_resident⟩
private theorem mu_ready : NodeReady machine ⟨domain,mu,mu⟩ := ⟨empty_domain machine,mu_available,mu_available⟩
private theorem mu_safe : SourceRecursiveIntersectionMemo.KeySafe 8 domain mu mu := by
  unfold SourceRecursiveIntersectionMemo.KeySafe
  refine ⟨by decide,by cbv,.mu 3,.mu 3,?_,?_,?_,?_⟩ <;> cbv

private def allocated : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula := ⟨.live 0 [],.top⟩
private def selectedEdge := (lookupEdge 8 request before.native).2
private def runningEdge := (demandEdge 0 selectedEdge).2
private def edgeStarted : Checked 8 := ⟨runningEdge,operations⟩
private def checkedOps := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le allocated allocated 0 0 operations).2
private def checkedEdge : Checked 8 := ⟨runningEdge,checkedOps⟩
private def madeEdge : Checked 8 := ⟨advance runningEdge {runningEdge.machine with heap := (run (makeEdge row.entry.key.symbol top []) heap).2},checkedOps⟩
private def edgeAfter : Checked 8 := ⟨SourceRecursiveIntersectionThunks.finishEdge 0 row madeEdge.native,checkedOps⟩
private theorem made_edge_heap : madeEdge.native.machine.heap = heap := by cbv
private theorem edge_after_machine : edgeAfter.native.machine = machine := by cbv
private theorem cold_edge : Trace 4 (.code (requestEdge domain row row)) before (.code (.pure row)) edgeAfter := by
  have one : step (.code (requestEdge domain row row)) before = .yielded
      ((Control.edgeBody request .pure).bind (fun value => .finishEdge 0 value (.pure value))) edgeStarted := by cbv
  have bodyStep : step (.edgeBody request .pure) edgeStarted = .yielded
      (.code (SourceEqualityNativeCheckedCode.children domain row row allocated)) checkedEdge := by cbv
  have built : Trace 1 (.code (SourceEqualityNativeCheckedCode.children domain row row allocated)) checkedEdge
      (.code (.pure row)) madeEdge := by
    refine Trace.cons (.code (SourceEqualityNativeCheckedCode.children domain row row allocated)) checkedEdge (.code (.pure row)) madeEdge (.code (.pure row)) madeEdge 0 ?_ ?_ (.refl _ _)
    · have shape : SourceEqualityNativeCheckedCode.children domain row row allocated =
          .work (makeEdge row.entry.key.symbol top []) .pure := by cbv
      rw [shape]
      exact SourceEqualityNativeDemandHeapPrimitives.WorkInputs.edge _ _ [] (by intro value member; cases member)
    · cbv
  have bodyTrace : Trace 2 (.edgeBody request .pure) edgeStarted (.code (.pure row)) madeEdge :=
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
  have first := SourceCurrentNativeEdgeWriterGrowth.History.trace started _ 4 row
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

private theorem captured_warm_proof :
    SourceCurrentNativeEdgeWriterGrowth.History advanced ∧
    SourceCurrentNativeEdgeWriterHistory.History advanced ∧
    advanced.native.edges.cells 0 = some ⟨request,.returned row⟩ ∧
    edgeAfter.native.machine.heap.edges.next < advanced.native.machine.heap.edges.next ∧
    Trace 1 (.code (requestEdge domain row row)) advanced (.code (.pure row)) advanced ∧
    SourceCurrentNativeEdgeWriterGrowth.Written (width := 8) 0 request row advanced.native.machine.heap ∧
    Writer (width := 8) request row := by
  have present : advanced.native.edges.cells 0 = some ⟨request,.returned row⟩ := by cbv
  have captured := advanced_history.warm advance_good request advanced.native advanced.native 0 row
    (advance_good.native.edges.checked 0 _ present).1 (by cbv) (by cbv) (by cbv)
  exact ⟨advanced_history,advanced_history.forget,present,by cbv,warm_after_advance,captured,captured.writer⟩
/-- The exact warm handle retains both earlier writer heaps after an actual allocating advance. -/
theorem captured_warm :
    SourceCurrentNativeEdgeWriterGrowth.History advanced ∧
    SourceCurrentNativeEdgeWriterHistory.History advanced ∧
    advanced.native.edges.cells 0 = some ⟨request,.returned row⟩ ∧
    edgeAfter.native.machine.heap.edges.next < advanced.native.machine.heap.edges.next ∧
    Trace 1 (.code (requestEdge domain row row)) advanced (.code (.pure row)) advanced ∧
    SourceCurrentNativeEdgeWriterGrowth.Written (width := 8) 0 request row advanced.native.machine.heap ∧
    Writer (width := 8) request row := captured_warm_proof
end MicroCFTA.NativeEdgeWriterGrowthKernels
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.NativeEdgeWriterGrowthKernels.captured_warm
#print MicroCFTA.NativeEdgeWriterGrowthKernels.captured_warm
#print axioms MicroCFTA.NativeEdgeWriterGrowthKernels.captured_warm
