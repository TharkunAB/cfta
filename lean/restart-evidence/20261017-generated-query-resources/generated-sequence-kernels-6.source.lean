import MicroCFTA.SourceCurrentConstrainedCapCheckedJointInventoryCold
import MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceCurrentConstrainedCapGeneratedQuerySequence
import MicroCFTA.EndpointMemoGateSource

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.GeneratedSequenceFixture
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
private def expression : Syntax Symbol Guard := .node [.mk ("roots", .top) top [
  .node [.mk ("a", .top) top [], .mk ("b", .top) top []],
  .node [.mk ("a", .top) top [], .mk ("c", .top) top []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD .empty
private def right : Value Symbol Guard := ((children root)[1]?).getD .empty
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def seedEqualities : Option EqualityNormalize.Constraints := some [[[0], [1]]]
private def seedBuild := SourceEqualityConstraintAllocation.construct seedEqualities Cache.emptyState
private def seedValue : SourceEqualityConstraintAllocation.Value := match seedBuild.1 with
  | .ok value => value
  | .error _ => .contradiction
private def seedState := SourceEqualityConstraintMemoAllocation.initial seedBuild.2
private def preparedOperations := (SourceEqualityConstraintMemoAllocation.descend seedValue 0 seedState).2
private def operations := SourceEqualityMkEdgeAllocation.emptyField preparedOperations

private theorem seed_cached : SourceEqualityGuardReadback.Cached seedEqualities := by
  have actual : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized actual

private theorem seed_constructed : seedBuild.1 = .ok seedValue := by cbv

private theorem prepared_valid : SourceEqualityConstraintMemoAllocation.Valid preparedOperations := by
  obtain ⟨value, cache, built, cacheValid, ready, _steps, _read, _classes⟩ :=
    SourceEqualityConstraintAllocation.construct_complete seedEqualities seed_cached Cache.emptyState Cache.empty_valid
  have same : value = seedValue := Except.ok.inj ((congrArg Prod.fst built).symm.trans seed_constructed)
  subst value
  have cacheSame : cache = seedBuild.2 := (congrArg Prod.snd built).symm
  subst cache
  exact (SourceEqualityConstraintMemoAllocation.descend_correct seedValue 0 seedState
    (SourceEqualityConstraintMemoAllocation.initial_valid _ cacheValid) ready).1
private def before (width : Nat) : Checked width := ⟨initial width machine, operations⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩

private theorem constructed : built = .done root heap := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, root, heap, done, InternedNestedConstruction.Outcome.state]

private theorem initial_good (width : Nat) : Good (before width) := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression, SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built, heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula) preparedOperations
    prepared_valid
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

private def row : EdgeValue Symbol Guard := match left with
  | .node _ (row :: _) _ _ => row
  | _ => (run (makeEdge ("unused", .top) top []) empty).1
private def candidate : Value Symbol Guard := (run (makeNode [row]) heap).1
private def nodeControl : Control (Value Symbol Guard) := .code (requestNode request.domain left right)
private noncomputable def afterFirst (width : Nat) : Checked width := (execute 8 nodeControl (before width)).state

private theorem evaluated (width : Nat) : execute 8 nodeControl (before width) = .done candidate (afterFirst width) := by
  set_option cbv.maxSteps 200000000 in cbv

private theorem candidate_absent : SourcePreparedSharedRows.read heap 3 = none := by cbv
private theorem operation_record : ∃ cell,
    operations.descents (seedValue.identity, 0) = some cell ∧
      SourceEqualityConstraintMemoAllocation.DescendGood operations.constraints (seedValue.identity, 0) cell := by
  have present : (operations.descents (seedValue.identity, 0)).isSome = true := by cbv
  cases found : operations.descents (seedValue.identity, 0) with
  | none => rw [found] at present; cases present
  | some cell => exact ⟨cell, rfl, (SourceEqualityMkEdgeAllocation.emptyField_correct preparedOperations prepared_valid).1.descents _ _ found⟩

private theorem candidate_input : SourceRecursiveIntersectionInputView.inputOf candidate = .node 3 := by cbv

private theorem candidate_outside : SourceRecursiveIntersectionInputView.inputOf candidate ∉
    SourceRecursiveIntersectionInputView.inventory heap := by
  rw [candidate_input]
  have count : heap.nodes.next = 3 := by cbv
  simp only [SourceRecursiveIntersectionInputView.inventory, count]
  decide

private theorem initial_semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression root heap constructed

private theorem initial_guards : SourceCurrentConstrainedCapGuardHeap.Heap
    SourceCurrentConstrainedCapCheckedJointClosed.Plain heap := by
  simpa only [built, heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap
    SourceCurrentConstrainedCapCheckedJointClosed.Plain expression

private theorem initial_ready (width : Nat) : SourceCurrentConjunctionClassScan.Ready (before width) := by
  have costs : InternedFreshOrdinaryCostHeap.Heap heap := by
    simpa only [built, heap] using InternedFreshOrdinaryCosts.closed_heap expression
  exact ⟨initial_good width, initial_semantic, costs,
    SourceCurrentAllocatedNativeScopeCache.initial_scoped width machine,
    SourceRecursiveIntersectionNative.idle_initial machine⟩

private theorem initial_caps : SourceCurrentConstrainedCap.Cap SourceCurrentConstrainedCapCheckedJointClosed.Plain 1 left ∧
    SourceCurrentConstrainedCap.Cap SourceCurrentConstrainedCapCheckedJointClosed.Plain 1 right := by
  constructor
  · cbv
    apply SourceCurrentConstrainedCap.Cap.node 0
    intro child member
    cbv at member
    cases member
  · cbv
    apply SourceCurrentConstrainedCap.Cap.node 0
    intro child member
    cbv at member
    cases member

private theorem initial_closed : left.free = [] ∧ right.free = [] := by constructor <;> cbv

private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedNativeInventoryCold.pairInventory heap
    (initial_good 0).native.machine.1 left right
    (SourceRecursiveIntersectionOriginalOutput.closed_original left heap (initial_good 0).native.machine.1.coherent
      originals.1 initial_closed.1)
    (SourceRecursiveIntersectionOriginalOutput.closed_original right heap (initial_good 0).native.machine.1.coherent
      originals.2 initial_closed.2)
    originals.1 originals.2 initial_closed.1 initial_closed.2

private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next, heap.edges.next, machine.domains.next, InternedValueMassHeap.initialBound heap⟩

private theorem initial_fits (width : Nat) : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile (before width) :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap (initial_good width).native.machine.1⟩

private theorem initial_pool (width : Nat) : SourceCurrentConstrainedCapGeneratedQuerySequence.Pool 1 [left, right] (before width) := by
  constructor
  · intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact originals.1
    · exact originals.2
  · intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact initial_closed.1
    · exact initial_closed.2
  · intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact initial_caps.1
    · exact initial_caps.2

/-- Literal source construction and actual first query produce a new node outside every original-source inventory. -/
theorem constructed_first (width : Nat) :
    built = .done root heap ∧
    SourceCurrentConjunctionClassScan.Ready (before width) ∧
    SourceCurrentConstrainedCapGuardHeap.Heap SourceCurrentConstrainedCapCheckedJointClosed.Plain heap ∧
    execute 8 nodeControl (before width) = .done candidate (afterFirst width) ∧
    SourceRecursiveIntersectionInputView.inputOf candidate = .node 3 ∧
    SourcePreparedSharedRows.read heap 3 = none ∧
    SourceRecursiveIntersectionInputView.inputOf candidate ∉ SourceRecursiveIntersectionInputView.inventory heap ∧
    (∀ (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
      (holds : Guard → Language.Term Symbol → Bool), inventory.source = heap →
      ¬(inventory.inputs holds).valid (SourceRecursiveIntersectionInputView.inputOf candidate)) ∧
    (afterFirst width).native.nodes.cells 0 = some ⟨request, .returned candidate⟩ ∧
    (afterFirst width).native.edges.cells 0 = some ⟨⟨IntersectionEmptyDomain.emptyDomain, row, row⟩, .returned row⟩ ∧
    ∃ cell, (afterFirst width).operations.descents (seedValue.identity, 0) = some cell ∧
      SourceEqualityConstraintMemoAllocation.DescendGood (afterFirst width).operations.constraints
        (seedValue.identity, 0) cell := by
  refine ⟨constructed, initial_ready width, initial_guards, evaluated width, candidate_input, candidate_absent,
    candidate_outside, ?_, ?_, ?_, ?_⟩
  · intro inventory holds same admitted
    have original := SourceCurrentAllocatedNativeInputInventoryModels.reachable_original inventory.source inventory.facts
      holds inventory.roots inventory.originals inventory.available inventory.closed _ admitted
    have member := original.inventory inventory.source inventory.facts _
    rw [same] at member
    exact candidate_outside member
  · set_option cbv.maxSteps 200000000 in cbv
  · set_option cbv.maxSteps 200000000 in cbv
  · have same : (afterFirst width).operations = operations := by
      set_option cbv.maxSteps 200000000 in cbv
    rw [same]
    exact operation_record

/-- One initial reservation constructs two queries. The second consumes the fresh first result. -/
theorem constructed_generated_sequence (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (reserved : SourceCurrentAllocatedNativeResourceForecast.Reserved bits profile 2) :
    ∃ second after next,
      SourceCurrentConstrainedCapGeneratedQuerySequence.Run 1 formulas solver EndpointMemoGateTrace.empty
        profile [(0, 1), (2, 1)] [left, right] (before (bits + 2)) [candidate, second] after ∧
      SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver next after ∧
      SourceCurrentConstrainedCapGeneratedQueryResources.Fits
        (SourceCurrentAllocatedNativeResourceForecast.advance profile 2) after ∧
      Extension (before (bits + 2)).native.machine after.native.machine ∧
      SourceCurrentConstrainedCapGeneratedQuerySequence.Pool 1 [left, right, candidate, second] after ∧
      EndpointMemoGateTrace.Valid after.native.machine.heap EndpointMemoGateTrace.empty ∧
      SourceCurrentAllocatedTargetQuery.Step candidate right (afterFirst (bits + 2)) second after ∧
      SourceRecursiveIntersectionInputView.inputOf candidate ∉ SourceRecursiveIntersectionInputView.inventory heap ∧
      (afterFirst (bits + 2)).native.nodes.cells 0 = some ⟨request, .returned candidate⟩ ∧
      (afterFirst (bits + 2)).native.edges.cells 0 = some ⟨⟨IntersectionEmptyDomain.emptyDomain, row, row⟩, .returned row⟩ ∧
      ∃ cell, (afterFirst (bits + 2)).operations.descents (seedValue.identity, 0) = some cell ∧
        SourceEqualityConstraintMemoAllocation.DescendGood (afterFirst (bits + 2)).operations.constraints
          (seedValue.identity, 0) cell := by
  have frame := SourceCurrentConstrainedCapGeneratedQueryResources.Frame.initial formulas solver inventory machine operations
    (initial_ready (bits + 2)) initial_guards rfl
  obtain ⟨results, after, next, run, finalFrame, finalFits, extension, pool, globals, _length⟩ :=
    SourceCurrentConstrainedCapGeneratedQuerySequence.complete_many profile 1 formulas solver [(0, 1), (2, 1)]
      [left, right] (by exact ⟨by decide, by decide, by decide, by decide, trivial⟩) reserved inventory (before (bits + 2)) frame (initial_fits (bits + 2))
      (initial_pool (bits + 2)) EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap)
  have actual := run
  cases actual with
  | cons leftFound rightFound firstReceipt tail =>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at leftFound rightFound
      cases leftFound
      cases rightFound
      obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedNativeColdClosedExact.completed_unique _ 8 nodeControl
        (before (bits + 2)) _ (afterFirst (bits + 2)) _ candidate firstReceipt.joint.done (evaluated (bits + 2))
      cases tail with
      | cons nextLeft nextRight secondReceipt finish =>
          simp only [List.cons_append, List.nil_append,
            List.getElem?_cons_zero, List.getElem?_cons_succ] at nextLeft nextRight
          cases nextLeft
          cases nextRight
          cases finish
          have initial := constructed_first (bits + 2)
          exact ⟨_, _, next, run, finalFrame, finalFits, extension, pool, globals,
            secondReceipt.query.actual, candidate_outside, initial.2.2.2.2.2.2.2.2.1,
            initial.2.2.2.2.2.2.2.2.2.1, initial.2.2.2.2.2.2.2.2.2.2⟩

end MicroCFTA.GeneratedSequenceFixture

#print axioms MicroCFTA.GeneratedSequenceFixture.constructed_first
#check @MicroCFTA.GeneratedSequenceFixture.constructed_first

#print axioms MicroCFTA.GeneratedSequenceFixture.constructed_generated_sequence
#check @MicroCFTA.GeneratedSequenceFixture.constructed_generated_sequence
