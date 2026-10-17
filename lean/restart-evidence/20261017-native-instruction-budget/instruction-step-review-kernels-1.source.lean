import MicroCFTA.SourceCurrentAllocatedNativeInstructionTrace
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputFinite
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

namespace MicroCFTA.InstructionStepReview
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
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
private def before : Checked 10 := ⟨initial 10 machine, operations⟩
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

private theorem shapes :
    SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape 2 1 left ∧
    SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape 2 1 right := by
  cbv

private theorem heights : max (MergedOrdinaryHeight.height left) (MergedOrdinaryHeight.height right) ≤ 2 := by cbv

private theorem original_key : ∃ key,
    SourceRecursiveIntersectionMemo.requestKey 10 request.domain request.left request.right = some key := by
  have present : (SourceRecursiveIntersectionMemo.requestKey 10 request.domain request.left request.right).isSome = true := by cbv
  cases found : SourceRecursiveIntersectionMemo.requestKey 10 request.domain request.left request.right with
  | none => rw [found] at present; cases present
  | some key => exact ⟨key, rfl⟩

private def nodeControl : Control (Value Symbol Guard) := .code (requestNode request.domain left right)

private def holds (_ : Guard) (_ : Language.Term Symbol) := true
private theorem source_facts : Facts heap := (InternedFreshOrdinaryFacts.closed_verified expression).facts
private theorem source_scope : NodeScope heap request :=
  initial_scope heap left right
    (SourceRecursiveIntersectionOriginalOutput.closed_original left heap source_facts.coherent originals.1 (by cbv))
    (SourceRecursiveIntersectionOriginalOutput.closed_original right heap source_facts.coherent originals.2 (by cbv))
    originals.1 originals.2
private theorem semantic_complete : Completes (view heap holds) (SourceRecursiveIntersectionNative.nodeSemantic request) :=
  SourceRecursiveIntersectionRequestProgress.initial_complete heap source_facts holds left right
    source_scope.left source_scope.right originals.1 originals.2 (by cbv) (by cbv)
private noncomputable def amount := SourceCurrentAllocatedNativeInstructionTrace.nodeBudget heap holds request
private def startedNative := (demandNode 0 (lookupNode 10 request before.native).2).2
private def started : Checked 10 := ⟨startedNative, before.operations⟩
private def startedControl : Control (Value Symbol Guard) :=
  .code ((compileNode request).bind (fun value => .finishNode 0 value (.pure value)))
private theorem first_step : step nodeControl before = .yielded startedControl started := by cbv
private theorem original_safe : SourceRecursiveIntersectionMemo.KeySafe 10 request.domain left right := by
  unfold SourceRecursiveIntersectionMemo.KeySafe
  refine ⟨by decide, by cbv, .node 1, .node 2, ?_, ?_, ?_, ?_⟩ <;> cbv
private theorem original_credit : SourceCurrentAllocatedNativeInstructionStep.ControlAt heap holds
    nodeControl before amount (fun after value => Available after.heap value) := by
  have charged : SourceRecursiveIntersectionInstructionCredit.NodeCharge heap holds
      (SourceRecursiveIntersectionInstructionProfile.sourceBranching heap) request amount := by
    refine ⟨source_scope, semantic_complete, ?_⟩
    rw [amount, SourceCurrentAllocatedNativeInstructionTrace.nodeBudget_of_complete heap holds request semantic_complete]
  exact SourceRecursiveIntersectionInstructionCredit.request_node request machine amount node_ready charged

/-- Own nonidentical checked roots pay a cold yielded step, every completed prefix, and an exact-state warm return from initial semantic credit. -/
theorem constructed_cold_warm_credit :
    built = .done root heap ∧ left ≠ right ∧
    step nodeControl before = .yielded startedControl started ∧
    started.native.nodes.cells 0 = some ⟨request, .evaluating⟩ ∧
    (∃ remaining, remaining + 1 ≤ amount ∧
      SourceCurrentAllocatedNativeInstructionStep.ControlAt heap holds startedControl started remaining
        (fun after value => Available after.heap value)) ∧
    ∃ fuel value after key handle,
      Trace fuel nodeControl before (.code (.pure value)) after ∧
      fuel ≤ amount ∧
      (∃ remaining, fuel + remaining ≤ amount ∧ Available after.native.machine.heap value) ∧
      after.native.nodes.table key = some handle ∧
      after.native.nodes.cells handle = some ⟨request, .returned value⟩ ∧
      Trace 1 nodeControl after (.code (.pure value)) after ∧
      execute 2 nodeControl after = .done value after ∧
      1 ≤ amount := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  obtain ⟨fuel, value, after, receipt, _idle, _semantic, _stored, _output, _shape, _height,
    _rightHeight, _closed, _capacity, _nodes, _edges⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOutputFinite.cold 8 2 1 2 (fun _ _ => true)
      before initial_good semantic rfl left right originals.1 originals.2 shapes.1 shapes.2 heights
      (by cbv) (by cbv)
  have firstInputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs nodeControl before :=
    ⟨node_ready, fun _ _ => original_safe⟩
  have firstCredit := SourceCurrentAllocatedNativeInstructionStep.yielded heap source_facts holds
    nodeControl startedControl before started amount (fun after value => Available after.heap value)
    initial_good firstInputs (fun _ => trivial) (grows_refl _) (extends_refl _) original_credit first_step
  have coldBound := SourceCurrentAllocatedNativeInstructionTrace.node_prefix heap source_facts holds request source_scope
    semantic_complete receipt.trace initial_good node_ready (grows_refl _) (extends_refl _)
  obtain ⟨remaining, paid, final⟩ := SourceCurrentAllocatedNativeInstructionTrace.prefix_bound heap source_facts holds
    receipt.trace initial_good (fun _ => trivial) (grows_refl _) (extends_refl _) original_credit
  obtain ⟨key, requested⟩ := original_key
  obtain ⟨⟨handle, published, returned⟩, repeated⟩ :=
    SourceCurrentAllocatedNativeCompletedMemo.repeat_of_trace fuel request before after value initial_good.native key requested receipt.trace
  have ready : NodeReady after.native.machine request :=
    ⟨node_ready.1.grows _ receipt.extension, receipt.extension.available _ originals.1,
      receipt.extension.available _ originals.2⟩
  have selected : lookupNode 10 request after.native = (.memoized handle, after.native) := by
    simp only [lookupNode, requested, FlatMemoThunk.lookupOrInsert, published]
  have demanded : demandNode handle after.native = (.ready value, after.native) := by
    simp only [demandNode, FlatMemoThunk.demand, returned]
  have one : step nodeControl after = .yielded (.code (.pure value)) after := by
    change lift after.operations (SourceRecursiveIntersectionNative.step
      SourceEqualityConstraintConstructors.top SourceEqualityPCSNativeEdge.conjoin (.node request .pure) after.native) = _
    simp only [SourceRecursiveIntersectionNative.step, selected, demanded, lift]
  have warm : Trace 1 nodeControl after (.code (.pure value)) after :=
    .cons _ _ _ _ _ _ 0 ⟨ready, fun _ _ => original_safe⟩ one (.refl _ _)
  have warmBound := SourceCurrentAllocatedNativeInstructionTrace.node_prefix heap source_facts holds request source_scope
    semantic_complete warm receipt.good ready receipt.extension.heap receipt.extension.history
  exact ⟨constructed, (by
    intro same
    have refs := congrArg Value.referenceOf same
    cbv at refs
    cases refs), first_step, by cbv, firstCredit, fuel, value, after, key, handle, receipt.trace,
    coldBound, remaining, paid, final, published, returned, warm, repeated, warmBound⟩

end MicroCFTA.InstructionStepReview

#print axioms MicroCFTA.InstructionStepReview.constructed_cold_warm_credit
#check @MicroCFTA.InstructionStepReview.constructed_cold_warm_credit
