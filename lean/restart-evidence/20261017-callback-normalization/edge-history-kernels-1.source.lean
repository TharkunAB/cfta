import MicroCFTA.SourceCurrentNativeEdgeHistory
import MicroCFTA.SourceEqualityNativeDemandMismatchProvenance
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.SourceEqualityAnnotationConstruction
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
noncomputable section
namespace MicroCFTA.NativeEdgeHistoryKernels
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

private theorem accepted_proof :
    ∃ (program : Syntax Symbol Guard) (initialState finalState : Checked 8) (output : EdgeValue Symbol Guard),
      InternedFreshOrdinaryConstruction.build program [] empty = .done root initialState.native.machine.heap ∧
      Trace 4 (.code (requestEdge domain row row)) initialState (.code (.pure output)) finalState ∧
      Trace 1 (.code (requestEdge domain row row)) finalState (.code (.pure output)) finalState ∧
      Writer (width := 8) request output ∧
      output.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin row.entry.key.constraint row.entry.key.constraint ∧
      ∃ (head middle tail : Checked 8) (values : List Node) (count : Nat),
        SourceCurrentAllocatedNativePhysicalCompletion.Good head ∧
        SourceCurrentAllocatedNativeSemanticTraceReadback.Walk (fun pair => requestNode domain pair.1 pair.2)
          (row.children.zip row.children) middle values tail count ∧ output.children = values := by
  have historical := SourceCurrentNativeEdgeHistory.warm (.code (requestEdge domain row row)) machine operations 4 row edgeAfter
    (by intro value; trivial) initial_good (by intro value; trivial) cold_edge request edgeAfter.native edgeAfter.native 0 row
    (by rw [edge_after_machine]; exact edge_ready) (by cbv) (by cbv) (by cbv)
  obtain ⟨head,middle,tail,values,count,good,walked,symbol,guard,children,rest⟩ := historical.live (by cbv)
  exact ⟨expression,before,edgeAfter,row,constructed,cold_edge,warm_edge,historical,guard,
    head,middle,tail,values,count,good,walked,children⟩

/-- Actual accepted cold publication and warm demand recover the joined guard and original ordered calls. -/
theorem accepted_warm :
    ∃ (program : Syntax Symbol Guard) (initialState finalState : Checked 8) (output : EdgeValue Symbol Guard),
      InternedFreshOrdinaryConstruction.build program [] empty = .done root initialState.native.machine.heap ∧
      Trace 4 (.code (requestEdge domain row row)) initialState (.code (.pure output)) finalState ∧
      Trace 1 (.code (requestEdge domain row row)) finalState (.code (.pure output)) finalState ∧
      Writer (width := 8) request output ∧
      output.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin row.entry.key.constraint row.entry.key.constraint ∧
      ∃ (head middle tail : Checked 8) (values : List Node) (count : Nat),
        SourceCurrentAllocatedNativePhysicalCompletion.Good head ∧
        SourceCurrentAllocatedNativeSemanticTraceReadback.Walk (fun pair => requestNode domain pair.1 pair.2)
          (row.children.zip row.children) middle values tail count ∧ output.children = values := accepted_proof

private def parentRow : EdgeValue Symbol Guard := match root with
  | .node _ (edge :: _) _ _ => edge
  | _ => row
private theorem parent_resident : EdgeResident heap parentRow := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  exact resident_edges heap initial_good.heap.semantic.1.normal.facts.linked root available.resident parentRow (by cbv; exact .head _)
private def rejectedRequest : EdgeRequest Symbol Guard := ⟨domain,parentRow,row⟩
private theorem rejected_ready : EdgeReady machine rejectedRequest := ⟨empty_domain machine,parent_resident,row_resident⟩
private def rejectedRunning := (demandEdge 0 (lookupEdge 8 rejectedRequest before.native).2).2
private def rejectedStarted : Checked 8 := ⟨rejectedRunning,operations⟩
private def rejectedChecked : Checked 8 := ⟨rejectedRunning,SourceEqualityMkEdgeAllocation.emptyField operations⟩
private def sentinel := (run (makeEdge parentRow.entry.key.symbol top [.empty]) heap).1
private def sentinelHeap := (run (makeEdge parentRow.entry.key.symbol top [.empty]) heap).2
private def rejectedMade : Checked 8 := ⟨advance rejectedRunning {rejectedRunning.machine with heap := sentinelHeap},rejectedChecked.operations⟩
private def rejectedAfter : Checked 8 := ⟨SourceRecursiveIntersectionThunks.finishEdge 0 sentinel rejectedMade.native,rejectedChecked.operations⟩
private theorem rejected_heap : rejectedAfter.native.machine.heap = sentinelHeap := by cbv
private theorem sentinel_available : Available heap (.empty : Node) := empty_available _
private theorem rejected_trace : Trace 4 (.code (requestEdge domain parentRow row)) before (.code (.pure sentinel)) rejectedAfter := by
  have built : Trace 1 (.code (SourceEqualityNativeCheckedCode.sentinel parentRow)) rejectedChecked (.code (.pure sentinel)) rejectedMade := by
    refine Trace.cons (.code (SourceEqualityNativeCheckedCode.sentinel parentRow)) rejectedChecked (.code (.pure sentinel)) rejectedMade
      (.code (.pure sentinel)) rejectedMade 0 ?_ ?_ (.refl _ _)
    · exact SourceEqualityNativeDemandHeapPrimitives.WorkInputs.edge _ _ [.empty] (by
        intro value member
        have same := List.mem_singleton.mp member
        subst value
        exact empty_available _)
    · cbv
  have bodyStep : step (.edgeBody rejectedRequest .pure) rejectedStarted =
      .yielded (.code (SourceEqualityNativeCheckedCode.sentinel parentRow)) rejectedChecked := by cbv
  have bodyTrace : Trace 2 (.edgeBody rejectedRequest .pure) rejectedStarted (.code (.pure sentinel)) rejectedMade :=
    .cons _ _ _ _ _ _ _ trivial bodyStep built
  have resident : EdgeResident rejectedMade.native.machine.heap sentinel := by
    change EdgeResident sentinelHeap sentinel
    exact (SourceEqualityNativeDemandMismatchProvenance.sentinel_provenance parentRow.entry.key.symbol heap initial_good.heap).2.1
  have finish : Trace 1 (.code (.finishEdge 0 sentinel (.pure sentinel))) rejectedMade (.code (.pure sentinel)) rejectedAfter := by
    refine Trace.cons (.code (.finishEdge 0 sentinel (.pure sentinel))) rejectedMade (.code (.pure sentinel)) rejectedAfter
      (.code (.pure sentinel)) rejectedAfter 0 ?_ rfl (.refl _ _)
    exact ⟨rejectedRequest,by cbv,resident⟩
  have firstStep : step (.code (requestEdge domain parentRow row)) before =
      .yielded ((Control.edgeBody rejectedRequest .pure).bind fun value => .finishEdge 0 value (.pure value)) rejectedStarted := by cbv
  exact .cons _ _ _ _ _ _ _ ⟨rejected_ready,by cbv⟩ firstStep
    ((bodyTrace.bind fun value => .finishEdge 0 value (.pure value)).trans finish)

private theorem rejected_proof :
    ∃ (program : Syntax Symbol Guard) (initialState finalState : Checked 8) (output : EdgeValue Symbol Guard),
      InternedFreshOrdinaryConstruction.build program [] empty = .done root initialState.native.machine.heap ∧
      Trace 4 (.code (requestEdge domain parentRow row)) initialState (.code (.pure output)) finalState ∧
      Trace 1 (.code (requestEdge domain parentRow row)) finalState (.code (.pure output)) finalState ∧
      parentRow.entry.key.symbol = row.entry.key.symbol ∧
      parentRow.children.length ≠ row.children.length ∧ Writer (width := 8) rejectedRequest output ∧
      output.children = [.empty] := by
  have good := SourceCurrentAllocatedNativeSemanticTraceReadback.effects rejected_trace initial_good (by intro value; trivial)
  have ready : EdgeReady rejectedAfter.native.machine rejectedRequest := by
    refine ⟨empty_domain _,good.2.2.1.edges _ parent_resident,good.2.2.1.edges _ row_resident⟩
  have historical := SourceCurrentNativeEdgeHistory.warm (.code (requestEdge domain parentRow row)) machine operations 4 sentinel rejectedAfter
    (by intro value; trivial) initial_good (by intro value; trivial) rejected_trace rejectedRequest rejectedAfter.native rejectedAfter.native 0 sentinel
    ready (by cbv) (by cbv) (by cbv)
  have repeated : Trace 1 (.code (requestEdge domain parentRow row)) rejectedAfter (.code (.pure sentinel)) rejectedAfter := by
    refine Trace.cons (.code (requestEdge domain parentRow row)) rejectedAfter (.code (.pure sentinel)) rejectedAfter
      (.code (.pure sentinel)) rejectedAfter 0 ⟨ready,by cbv⟩ ?_ (.refl _ _)
    cbv
  exact ⟨expression,before,rejectedAfter,sentinel,constructed,rejected_trace,repeated,by cbv,by cbv,historical,
    (SourceEqualityNativeDemandMismatchProvenance.sentinel_provenance parentRow.entry.key.symbol heap initial_good.heap).2.2.2.2.1⟩

/-- Actual unequal-arity cold and warm calls retain a causal writer for the literal sentinel. -/
theorem sentinel_warm :
    ∃ (program : Syntax Symbol Guard) (initialState finalState : Checked 8) (output : EdgeValue Symbol Guard),
      InternedFreshOrdinaryConstruction.build program [] empty = .done root initialState.native.machine.heap ∧
      Trace 4 (.code (requestEdge domain parentRow row)) initialState (.code (.pure output)) finalState ∧
      Trace 1 (.code (requestEdge domain parentRow row)) finalState (.code (.pure output)) finalState ∧
      parentRow.entry.key.symbol = row.entry.key.symbol ∧
      parentRow.children.length ≠ row.children.length ∧ Writer (width := 8) rejectedRequest output ∧
      output.children = [.empty] := rejected_proof
end MicroCFTA.NativeEdgeHistoryKernels
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.NativeEdgeHistoryKernels.accepted_warm
#print MicroCFTA.NativeEdgeHistoryKernels.accepted_warm
#print axioms MicroCFTA.NativeEdgeHistoryKernels.accepted_warm
#check @MicroCFTA.NativeEdgeHistoryKernels.sentinel_warm
#print MicroCFTA.NativeEdgeHistoryKernels.sentinel_warm
#print axioms MicroCFTA.NativeEdgeHistoryKernels.sentinel_warm
