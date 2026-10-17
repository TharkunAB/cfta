import MicroCFTA.SourceCurrentNativeCausalEntry
import MicroCFTA.InternedFreshOrdinaryCosts
import MicroCFTA.SourceEqualityNativeDemandMismatchProvenance
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.SourceEqualityAnnotationConstruction
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
noncomputable section
namespace MicroCFTA.NativeCausalEntryKernels
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



private noncomputable instance : DecidableEq Node := by classical exact inferInstance
private theorem cold_good : Good edgeAfter :=
  (SourceCurrentAllocatedNativeSemanticTraceReadback.effects cold_edge initial_good (by intro value; trivial)).1
private theorem cold_history : SourceCurrentNativeEdgeWriterGrowth.History edgeAfter :=
  .trace (.initial machine operations) _ 4 row (by intro value; trivial) initial_good (by intro value; trivial) cold_edge
private theorem cold_semantic : SourceEqualityRequiredSemanticCache.SemanticReady edgeAfter.native.machine.heap := by
  rw [edge_after_machine]
  exact SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
private theorem cold_costs : InternedFreshOrdinaryCostHeap.Heap edgeAfter.native.machine.heap := by
  rw [edge_after_machine]
  exact InternedFreshOrdinaryCosts.closed_heap expression
private theorem cold_idle : SourceRecursiveIntersectionNative.Idle edgeAfter.native :=
  SourceCurrentAllocatedNativeRunning.done_idle 5 _ before edgeAfter row (by intro value; trivial)
    initial_good.native.shape (SourceRecursiveIntersectionNative.idle_initial machine)
    (trace_done 4 _ before edgeAfter row cold_edge.steps)
private theorem cold_mu_available : Available edgeAfter.native.machine.heap mu := by
  rw [edge_after_machine]
  exact mu_available

private theorem admitted_rows {table after}
    (actual : SourceCurrentConjunctionWorklist.Run 3 [] [[mu]]
      (SourceCurrentAllocatedNativeEffects.physical edgeAfter) table after) :
    ∃ requirements middle, SourceCurrentConjunctionRowsAllocation.Rows [mu]
      (SourceCurrentAllocatedNativeEffects.physical edgeAfter) requirements middle := by
  cases actual with
  | empty impossible rest =>
      have nonempty : ([mu] : List Node).any SourceCurrentConjunctionRequirements.isEmpty = false := by cbv
      rw [nonempty] at impossible
      cases impossible
  | skip nonempty skipped rest =>
      have admitted : SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
          SourceCurrentConjunctionWorklist.closed 3 [] [mu] = false := by cbv
      rw [admitted] at skipped
      cases skipped
  | admit nonempty fresh rows rest => exact ⟨_,_,rows⟩

private theorem conjunction_proof (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ answer after saved requirements middle,
      SourceCurrentConjunctionMemo.Call 3 SourceCurrentEmptinessMemo.empty mu
        (SourceCurrentAllocatedNativeEffects.physical edgeAfter) answer after saved ∧
      SourceCurrentAllocatedConjunctionMemo.Receipt edgeAfter after ∧
      SourceCurrentNativeEdgeWriterGrowth.History (SourceCurrentAllocatedQueryMemo.advancePhysical edgeAfter after) ∧
      (SourceCurrentAllocatedQueryMemo.advancePhysical edgeAfter after).native.edges.cells 0 = some ⟨request,.returned row⟩ ∧
      SourceCurrentNativeEdgeWriterGrowth.Written (width := 8) 0 request row after.heap ∧
      SourceCurrentConjunctionRowsAllocation.Rows [mu]
        (SourceCurrentAllocatedNativeEffects.physical edgeAfter) requirements middle ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver mu answer := by
  obtain ⟨answer,after,saved,actual,receipt,history,correct,sound,retained⟩ :=
    SourceCurrentNativeCausalEntry.conjunction formulas solver 3 SourceCurrentEmptinessMemo.empty mu edgeAfter
      cold_history cold_good cold_semantic cold_costs cold_idle cold_mu_available
      (SourceCurrentEmptinessMemo.empty_correct formulas solver _)
  have present : (SourceCurrentAllocatedQueryMemo.advancePhysical edgeAfter after).native.edges.cells 0 =
      some ⟨request,.returned row⟩ := by
    rw [receipt.tables.2.1]
    cbv
  have captured := history.writers 0 request row present
  have rows : ∃ requirements middle, SourceCurrentConjunctionRowsAllocation.Rows [mu]
      (SourceCurrentAllocatedNativeEffects.physical edgeAfter) requirements middle := by
    cases actual with
    | hit found => cases found
    | miss absent decision =>
        cases decision with
        | open_input openInput =>
            have closed : SourceCurrentConjunctionWorklist.closed mu = true := by cbv
            rw [closed] at openInput
            cases openInput
        | closed closedInput explored grown => exact admitted_rows explored
  obtain ⟨requirements,middle,exposed⟩ := rows
  exact ⟨answer,after,saved,requirements,middle,actual,receipt,history,present,captured,exposed,correct,sound⟩

/-- Initial source facts construct a nonempty conjunction read and retain the earlier native handle and writer heaps. -/
theorem conjunction_retains_writer (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ answer after saved requirements middle,
      SourceCurrentConjunctionMemo.Call 3 SourceCurrentEmptinessMemo.empty mu
        (SourceCurrentAllocatedNativeEffects.physical edgeAfter) answer after saved ∧
      SourceCurrentAllocatedConjunctionMemo.Receipt edgeAfter after ∧
      SourceCurrentNativeEdgeWriterGrowth.History (SourceCurrentAllocatedQueryMemo.advancePhysical edgeAfter after) ∧
      (SourceCurrentAllocatedQueryMemo.advancePhysical edgeAfter after).native.edges.cells 0 = some ⟨request,.returned row⟩ ∧
      SourceCurrentNativeEdgeWriterGrowth.Written (width := 8) 0 request row after.heap ∧
      SourceCurrentConjunctionRowsAllocation.Rows [mu]
        (SourceCurrentAllocatedNativeEffects.physical edgeAfter) requirements middle ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver mu answer := conjunction_proof formulas solver
end MicroCFTA.NativeCausalEntryKernels
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.NativeCausalEntryKernels.conjunction_retains_writer
#print MicroCFTA.NativeCausalEntryKernels.conjunction_retains_writer
#print axioms MicroCFTA.NativeCausalEntryKernels.conjunction_retains_writer
