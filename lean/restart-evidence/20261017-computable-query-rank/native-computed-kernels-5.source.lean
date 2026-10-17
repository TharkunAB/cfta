import MicroCFTA.SourceCurrentAllocatedNativeComputedBudget
import MicroCFTA.InternedValueMassConstructors
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

namespace MicroCFTA.NativeComputedKernels
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
private def sourceMass := InternedValueMassHeap.initialBound heap
private def amount := SourceCurrentAllocatedNativeComputedBudget.instructionBound heap.nodes.next heap.edges.next sourceMass
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
theorem computed_ordinary_cold_warm :
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
    SourceCurrentAllocatedNativeComputedBudget.initial 24 holds before initial_good semantic (SourceRecursiveIntersectionNative.idle_initial machine)
      left right leftOriginal rightOriginal originals.1 originals.2 (by cbv) (by cbv)
      (InternedValueMassHeap.initial heap initial_good.native.machine.1) (by cbv) (by cbv) (by cbv)
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

private def simpleExpression : Syntax Symbol Guard := .node [.mk ("constant", .top) top []]
private def simpleEdge := run (makeEdge ("constant", FullSyntax.Formula.top) top []) (empty : State Symbol Guard)
private def simpleNode := run (makeNode [simpleEdge.1]) simpleEdge.2
private def simpleMachine : Machine Symbol Guard := ⟨simpleNode.2, Cache.emptyState⟩
private def simpleBefore : Checked 6 := ⟨initial 6 simpleMachine, operations⟩
private def simpleRequest : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, simpleNode.1, simpleNode.1⟩
private def simpleControl : Control (Value Symbol Guard) := .code (requestNode simpleRequest.domain simpleNode.1 simpleNode.1)

private theorem simple_built : InternedFreshOrdinaryConstruction.build simpleExpression [] empty = .done simpleNode.1 simpleNode.2 := by cbv

private theorem simple_good : Good simpleBefore := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed simpleExpression simpleNode.1 simpleNode.2 simple_built
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) simpleNode.2 := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) simpleExpression
      (by simp [simpleExpression, SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [simple_built, InternedNestedConstruction.Outcome.state] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid simpleMachine
    ⟨semantic.ready.semantic.1.normal.facts, Cache.empty_valid⟩, semantic.ready, loaded.1, ?_⟩
  intro key row found
  rw [guarded key row found]
  exact loaded.2.2

private theorem simple_stored : InternedValueMassHeap.Stored 3 simpleNode.2 := by
  have row := InternedValueMassConstructors.edge ("constant", FullSyntax.Formula.top) top [] (empty : State Symbol Guard)
    (InternedValueMassHeap.empty_stored (by decide : 1 ≤ 1))
  have node := InternedValueMassConstructors.node [simpleEdge.1] simpleEdge.2 row.1
  have numeric : max (max 1 (1 + InternedValueMass.values ([] : List (Value Symbol Guard))))
      (1 + InternedValueMass.edges [simpleEdge.1]) = 3 := by cbv
  simpa only [numeric, simpleNode] using node.1

private theorem simple_sum : InternedValueMassHeap.initialBound simpleNode.2 = 5 := by cbv

private theorem simple_complete (mass : Nat) (initialStored : InternedValueMassHeap.Stored mass simpleNode.2) :
    let bound := SourceCurrentAllocatedNativeComputedBudget.instructionBound
      simpleBefore.native.machine.heap.nodes.next simpleBefore.native.machine.heap.edges.next mass
    ∃ fuel value after,
      SourceCurrentAllocatedNativePhysicalTraceCompletion.Receipt fuel simpleControl simpleBefore value after
        (fun final result => Available final.heap result) ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ fuel ≤ bound ∧
      execute (bound + 1) simpleControl simpleBefore = .done value after ∧
      InternedValueMassHeap.Stored (SourceCurrentAllocatedRecursiveMassTrace.massAfter bound mass) after.native.machine.heap ∧
      InternedValueMass.value value ≤ SourceCurrentAllocatedRecursiveMassTrace.massAfter bound mass ∧
      after.native.machine.heap.nodes.next ≤ simpleNode.2.nodes.next + SourceCurrentAllocatedRecursiveMassTrace.credit bound mass ∧
      after.native.machine.heap.edges.next ≤ simpleNode.2.edges.next + SourceCurrentAllocatedRecursiveMassTrace.credit bound mass ∧
      after.native.machine.domains.next ≤ simpleBefore.native.machine.domains.next + bound := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed simpleExpression simpleNode.1 simpleNode.2 simple_built
  have available := (InternedFreshOrdinaryFacts.closed_verified simpleExpression).result simpleNode.1 simpleNode.2 simple_built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty simpleExpression simpleNode.1 simpleNode.2 simple_built
  have original := SourceRecursiveIntersectionOriginalOutput.closed_original simpleNode.1 simpleNode.2
    simple_good.native.machine.1.coherent available closed
  obtain ⟨fuel, value, after, receipt, idle, count, done, stored, mass, nodes, edges, domains⟩ :=
    SourceCurrentAllocatedNativeComputedBudget.initial 4 holds simpleBefore simple_good semantic
      (SourceRecursiveIntersectionNative.idle_initial simpleMachine) simpleNode.1 simpleNode.1 original original
      available available closed closed initialStored (by cbv) (by cbv) (by cbv)
  exact ⟨fuel, value, after, receipt, idle, count, done, stored, mass, nodes, edges, domains⟩


/-- A smaller causal payload bound drives the exact constructed query instead of its larger recomputed initial sum. -/
theorem computed_causal_mass :
    InternedFreshOrdinaryConstruction.build simpleExpression [] empty = .done simpleNode.1 simpleNode.2 ∧
    InternedValueMassHeap.Stored 3 simpleNode.2 ∧ InternedValueMassHeap.initialBound simpleNode.2 = 5 ∧
    let bound := SourceCurrentAllocatedNativeComputedBudget.instructionBound
      simpleBefore.native.machine.heap.nodes.next simpleBefore.native.machine.heap.edges.next 3
    ∃ fuel value after,
      SourceCurrentAllocatedNativePhysicalTraceCompletion.Receipt fuel simpleControl simpleBefore value after
        (fun final result => Available final.heap result) ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ fuel ≤ bound ∧
      execute (bound + 1) simpleControl simpleBefore = .done value after ∧
      InternedValueMassHeap.Stored (SourceCurrentAllocatedRecursiveMassTrace.massAfter bound 3) after.native.machine.heap ∧
      InternedValueMass.value value ≤ SourceCurrentAllocatedRecursiveMassTrace.massAfter bound 3 ∧
      after.native.machine.heap.nodes.next ≤ simpleNode.2.nodes.next + SourceCurrentAllocatedRecursiveMassTrace.credit bound 3 ∧
      after.native.machine.heap.edges.next ≤ simpleNode.2.edges.next + SourceCurrentAllocatedRecursiveMassTrace.credit bound 3 ∧
      after.native.machine.domains.next ≤ simpleBefore.native.machine.domains.next + bound := by
  exact ⟨simple_built, simple_stored, simple_sum, simple_complete 3 simple_stored⟩

end MicroCFTA.NativeComputedKernels

#print axioms MicroCFTA.NativeComputedKernels.computed_ordinary_cold_warm
#check @MicroCFTA.NativeComputedKernels.computed_ordinary_cold_warm
#print axioms MicroCFTA.NativeComputedKernels.computed_causal_mass
#check @MicroCFTA.NativeComputedKernels.computed_causal_mass
