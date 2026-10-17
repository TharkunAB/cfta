import MicroCFTA.SourceCurrentNativePublicationTrace
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
set_option pp.proofs.threshold 254
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.NativePublicationTraceChecks
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
  .node [.mk ("step", .top) top [base], .mk ("other", .top) top []], .binder true base]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD .empty
private def right : Value Symbol Guard := ((children root)[1]?).getD .empty
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def operations := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def before : Checked 66 := ⟨initial 66 machine, operations⟩
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
private def startedNative := (demandNode 0 (lookupNode 66 request before.native).2).2
private def started : Checked 66 := ⟨startedNative, before.operations⟩
private def startedControl : Control (Value Symbol Guard) :=
  .code ((compileNode request).bind (fun value => .finishNode 0 value (.pure value)))
private theorem first_step : step nodeControl before = .yielded startedControl started := by cbv
private theorem original_key : ∃ key,
    SourceRecursiveIntersectionMemo.requestKey 66 request.domain request.left request.right = some key := by
  have present : (SourceRecursiveIntersectionMemo.requestKey 66 request.domain request.left request.right).isSome = true := by cbv
  cases found : SourceRecursiveIntersectionMemo.requestKey 66 request.domain request.left request.right with
  | none => rw [found] at present; cases present
  | some key => exact ⟨key, rfl⟩


private def baseValue : Value Symbol Guard := ((children left)[0]?).getD .empty
private def unusedKey := InternedConstructorTemplates.muKey baseValue baseValue

private theorem unused_stored : ∃ entry body depth ordinary,
    heap.nodeRecords unusedKey = some (.mu entry body depth ordinary) ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false := by
  exact ⟨_, _, _, _, by cbv, by cbv⟩

/-- An own source-built checked query retains its protected returned cell and causal unused-Mu law on warm replay. -/
theorem actual_cold_warm :
    built = .done root heap ∧ left ≠ right ∧
    step nodeControl before = .yielded startedControl started ∧
    started.native.nodes.cells 0 = some ⟨request, .evaluating⟩ ∧
    ∃ fuel value after key handle,
      SourceCurrentAllocatedNativePhysicalTraceCompletion.Receipt fuel nodeControl before value after
        (fun final result => Available final.heap result) ∧
      SourceRecursiveIntersectionSemanticHeap.SemanticHeap after.native.machine.heap ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty after.native.machine.heap) ∧
      after.native.nodes.table key = some handle ∧
      after.native.nodes.cells handle = some ⟨request, .returned value⟩ ∧
      execute 2 nodeControl after = .done value after ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty
        (execute 2 nodeControl after).state.native.machine.heap) ∧
      ∃ entry body depth ordinary,
        after.native.machine.heap.nodeRecords unusedKey = some (.mu entry body depth ordinary) ∧
        InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false ∧
        InternedNestedConstruction.finish true (.mu entry body depth ordinary) =
          SourceCurrentNativeCallbackErasure.eraseSelf
            (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) ordinary := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have facts := initial_good.native.machine.1
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left heap facts.coherent originals.1 (by cbv)
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right heap facts.coherent originals.2 (by cbv)
  obtain ⟨fuel, value, after, receipt, _, _, _, _, _, _, _, _⟩ :=
    SourceCurrentAllocatedNativeInitialInstructionBudget.initial 64 holds before initial_good semantic
      (SourceRecursiveIntersectionNative.idle_initial machine)
      left right leftOriginal rightOriginal originals.1 originals.2 (by cbv) (by cbv)
      (by cbv) (by cbv) (by cbv)
  obtain ⟨key, requested⟩ := original_key
  obtain ⟨⟨handle, published, returned⟩, repeated⟩ :=
    SourceCurrentAllocatedNativeCompletedMemo.repeat_of_trace fuel request before after value
      initial_good.native key requested receipt.trace
  obtain ⟨retained, history⟩ := SourceCurrentNativePublicationTrace.source_trace expression receipt.trace rfl
  obtain ⟨entry, body, depth, ordinary, present, unused⟩ := unused_stored
  have later := receipt.extension.heap.nodeRecords unusedKey _ present
  have law := SourceCurrentNativePublicationTrace.source_unused expression receipt.trace rfl
    unusedKey entry body depth ordinary later unused
  refine ⟨constructed, ?_, first_step, by cbv, fuel, value, after, key, handle,
    receipt, retained, history, published, returned, repeated, ?_, entry, body, depth, ordinary, later, unused, law⟩
  · intro same
    have refs := congrArg Value.referenceOf same
    cbv at refs
    cases refs
  · simpa only [repeated, Outcome.state] using history

private def mixedExpression : Syntax Symbol Guard := .union [
  .binder false (.node [.mk ("loop", .top) top [.var 0]]), base]
private def mixedBuilt := InternedFreshOrdinaryConstruction.build mixedExpression [] empty
private def mixedRoot : Value Symbol Guard := match mixedBuilt with | .done value _ => value | .pending .. => .empty
private def mixedHeap := mixedBuilt.state
private def mixedLeft : Value Symbol Guard := ((children mixedRoot)[0]?).getD .empty
private def mixedMachine : Machine Symbol Guard := ⟨mixedHeap, Cache.emptyState⟩
private def mixedBefore : Checked 130 := ⟨initial 130 mixedMachine, operations⟩
private def mixedRequest : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, mixedLeft, mixedRoot⟩
private noncomputable def mixedAmount := SourceCurrentAllocatedNativeInstructionTrace.nodeBudget mixedHeap holds mixedRequest
private def mixedControl : Control (Value Symbol Guard) := .code (requestNode mixedRequest.domain mixedLeft mixedRoot)

private theorem mixed_constructed : mixedBuilt = .done mixedRoot mixedHeap := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete mixedExpression
  simp only [mixedBuilt, mixedRoot, mixedHeap, done, InternedNestedConstruction.Outcome.state]

private theorem mixed_good : Good mixedBefore := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed mixedExpression mixedRoot mixedHeap mixed_constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) mixedHeap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) mixedExpression
      (by simp [mixedExpression, base, SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [mixedBuilt, mixedHeap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid mixedMachine
    ⟨semantic.ready.semantic.1.normal.facts, Cache.empty_valid⟩, semantic.ready, loaded.1, ?_⟩
  intro key row found
  rw [guarded key row found]
  exact loaded.2.2

/-- A recursive Mu/union source constructs its own complete native trace before the history producer is applied. -/
theorem actual_recursive_mu_union :
    mixedBuilt = .done mixedRoot mixedHeap ∧
    (∃ entry body depth ordinary, mixedLeft = .mu entry body depth ordinary) ∧
    (∃ entry members depth free, mixedRoot = .union entry members depth free ∧ members.length = 2) ∧
    mixedLeft ≠ mixedRoot ∧
    ∃ fuel value after,
      SourceCurrentAllocatedNativePhysicalTraceCompletion.Receipt fuel mixedControl mixedBefore value after
        (fun final result => Available final.heap result) ∧
      SourceRecursiveIntersectionSemanticHeap.SemanticHeap after.native.machine.heap ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty after.native.machine.heap) ∧
      execute (fuel + 1) mixedControl mixedBefore = .done value after := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed mixedExpression mixedRoot mixedHeap mixed_constructed
  have available := (InternedFreshOrdinaryFacts.closed_verified mixedExpression).result mixedRoot mixedHeap mixed_constructed
  have firstAvailable := available.children mixedLeft (by cbv; exact .head _)
  have facts := mixed_good.native.machine.1
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original mixedLeft mixedHeap facts.coherent firstAvailable (by cbv)
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original mixedRoot mixedHeap facts.coherent available
    (InternedFreshOrdinarySourceFreeNames.closed_free_empty mixedExpression mixedRoot mixedHeap mixed_constructed)
  obtain ⟨fuel, value, after, receipt, _, _, _, _, _, _, _, _⟩ :=
    SourceCurrentAllocatedNativeInitialInstructionBudget.initial 128 holds mixedBefore mixed_good semantic
      (SourceRecursiveIntersectionNative.idle_initial mixedMachine)
      mixedLeft mixedRoot leftOriginal rightOriginal firstAvailable available (by cbv)
      (InternedFreshOrdinarySourceFreeNames.closed_free_empty mixedExpression mixedRoot mixedHeap mixed_constructed)
      (by cbv) (by cbv) (by cbv)
  obtain ⟨retained, history⟩ := SourceCurrentNativePublicationTrace.source_trace mixedExpression receipt.trace rfl
  refine ⟨mixed_constructed, ?_, ?_, ?_, fuel, value, after, receipt, retained, history, receipt.done⟩
  · exact ⟨_, _, _, _, by cbv⟩
  · exact ⟨_, _, _, _, by cbv, by cbv⟩
  · intro same
    have refs := congrArg Value.referenceOf same
    cbv at refs
    cases refs

end MicroCFTA.NativePublicationTraceChecks

#check @MicroCFTA.NativePublicationTraceChecks.actual_cold_warm
#print axioms MicroCFTA.NativePublicationTraceChecks.actual_cold_warm
#check @MicroCFTA.NativePublicationTraceChecks.actual_recursive_mu_union
#print axioms MicroCFTA.NativePublicationTraceChecks.actual_recursive_mu_union
