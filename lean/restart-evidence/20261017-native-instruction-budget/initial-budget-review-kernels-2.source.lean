import MicroCFTA.SourceCurrentAllocatedNativeInitialInstructionBudget
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.InitialBudgetReview
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand IntersectSchedule SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def top : Guard := SourceEqualityConstraintConstructors.top
private def base : Syntax Symbol Guard := .node [.mk ("base", .top) top []]
private def expression : Syntax Symbol Guard := .node [.mk ("roots", .top) top [
  .node [.mk ("step", .top) top [base]],
  .node [.mk ("step", .top) top [base], .mk ("other", .top) top []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD .empty
private def right : Value Symbol Guard := ((children root)[1]?).getD .empty
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def operations := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def before : Checked 26 := ⟨initial 26 machine, operations⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩

private theorem constructed : built = .done root heap := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, root, heap, done, InternedNestedConstruction.Outcome.state]

private theorem initial_good : Good before := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression, base, SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built, heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula) SourceEqualityConstraintMemoAllocation.empty
    SourceEqualityConstraintMemoAllocation.empty_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
    ⟨semantic.ready.semantic.1.normal.facts, Cache.empty_valid⟩, semantic.ready, loaded.1, ?_⟩
  intro key row found
  have same := guarded key row found
  rw [same]
  exact loaded.2.2

private theorem originals : Available heap left ∧ Available heap right := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  constructor
  · exact available.children left (by cbv; exact .head _)
  · exact available.children right (by cbv; exact .tail _ (.head _))

private theorem node_ready : NodeReady machine request := ⟨empty_domain machine, originals.1, originals.2⟩

private def holds (_ : Guard) (_ : Language.Term Symbol) := true
private noncomputable def amount := SourceCurrentAllocatedNativeInstructionTrace.nodeBudget heap holds request
private def nodeControl : Control (Value Symbol Guard) := .code (requestNode request.domain left right)
private def startedNative := (demandNode 0 (lookupNode 26 request before.native).2).2
private def started : Checked 26 := ⟨startedNative, before.operations⟩
private def startedControl : Control (Value Symbol Guard) :=
  .code ((compileNode request).bind (fun value => .finishNode 0 value (.pure value)))
private theorem first_step : step nodeControl before = .yielded startedControl started := by cbv
private theorem original_key : ∃ key,
    SourceRecursiveIntersectionMemo.requestKey 26 request.domain request.left request.right = some key := by
  have present : (SourceRecursiveIntersectionMemo.requestKey 26 request.domain request.left request.right).isSome = true := by cbv
  cases found : SourceRecursiveIntersectionMemo.requestKey 26 request.domain request.left request.right with
  | none => rw [found] at present; cases present
  | some key => exact ⟨key, rfl⟩

/-- Initial source facts construct a cold checked ordinary query and an exact warm replay on its returned tables. -/
theorem initial_ordinary_cold_warm :
    built = .done root heap ∧ left ≠ right ∧
    step nodeControl before = .yielded startedControl started ∧
    started.native.nodes.cells 0 = some ⟨request, .evaluating⟩ ∧
    (∃ edge next state, execute 2 nodeControl before = .yielded (.edgeBody edge next) state) ∧
    ∃ fuel value after key handle,
      SourceCurrentAllocatedNativePhysicalTraceCompletion.Receipt fuel nodeControl before value after
        (fun final result => Available final.heap result) ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ fuel ≤ amount ∧
      execute (amount + 1) nodeControl before = .done value after ∧
      InternedValueMassHeap.Stored
        (SourceCurrentAllocatedRecursiveMassTrace.massAfter amount (InternedValueMassHeap.initialBound heap)) after.native.machine.heap ∧
      InternedValueMass.value value ≤
        SourceCurrentAllocatedRecursiveMassTrace.massAfter amount (InternedValueMassHeap.initialBound heap) ∧
      after.native.machine.heap.nodes.next ≤ heap.nodes.next +
        SourceCurrentAllocatedRecursiveMassTrace.credit amount (InternedValueMassHeap.initialBound heap) ∧
      after.native.machine.heap.edges.next ≤ heap.edges.next +
        SourceCurrentAllocatedRecursiveMassTrace.credit amount (InternedValueMassHeap.initialBound heap) ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + amount ∧
      after.native.nodes.table key = some handle ∧
      after.native.nodes.cells handle = some ⟨request, .returned value⟩ ∧
      execute 2 nodeControl after = .done value after := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have facts := initial_good.native.machine.1
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left heap facts.coherent originals.1 (by cbv)
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right heap facts.coherent originals.2 (by cbv)
  obtain ⟨fuel, value, after, receipt, idle, counted, executed, stored, mass, nodes, edges, domains⟩ :=
    SourceCurrentAllocatedNativeInitialInstructionBudget.initial 24 holds before initial_good semantic (SourceRecursiveIntersectionNative.idle_initial machine)
      left right leftOriginal rightOriginal originals.1 originals.2 (by cbv) (by cbv)
      (by cbv) (by cbv) (by cbv)
  obtain ⟨key, requested⟩ := original_key
  obtain ⟨⟨handle, published, returned⟩, repeated⟩ :=
    SourceCurrentAllocatedNativeCompletedMemo.repeat_of_trace fuel request before after value initial_good.native key requested receipt.trace
  refine ⟨constructed, ?_, first_step, by cbv, ?_, fuel, value, after, key, handle,
    receipt, idle, counted, executed, stored, mass, nodes, edges, domains, published, returned, repeated⟩
  · intro same
    have refs := congrArg Value.referenceOf same
    cbv at refs
    cases refs
  · set_option cbv.maxSteps 200000000 in
      exact ⟨_, _, _, by cbv⟩

end MicroCFTA.InitialBudgetReview

#print axioms MicroCFTA.InitialBudgetReview.initial_ordinary_cold_warm
#check @MicroCFTA.InitialBudgetReview.initial_ordinary_cold_warm
