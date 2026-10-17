import MicroCFTA.SourceCurrentScanNumeric
import MicroCFTA.SourceCurrentAllocatedScanWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedScanWorkerStability
import MicroCFTA.SourceCurrentGateFrameResources
import MicroCFTA.SourceCurrentSeededCallerNumeric
import MicroCFTA.SourceCurrentGeneratedQueryFrameResources
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentAllocatedNativeInventoryCold
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
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

namespace MicroCFTA.ScanNumericIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => SourceCurrentConstrainedCapCheckedJointClosed.Plain
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def annotation : Guard := ⟨some [[[0], [1]]], .top⟩
private def expression : Syntax Symbol Guard :=
  .node [.mk ("leaf", .top) annotation []]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def allocated := SourceEqualityConstraintAllocation.construct annotation.equalities Cache.emptyState
private def field : SourceEqualityConstraintAllocation.Value := match allocated.1 with
  | .ok value => value
  | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial allocated.2
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def before (width : Nat) : Checked width := ⟨initial width machine, operations⟩

private theorem cached : SourceEqualityGuardReadback.Cached annotation.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem allocation : allocated = (.ok field, allocated.2) := by cbv
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocated.2 [annotation] := by
  simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
    (.start Cache.emptyState) cached allocation
private theorem constructed : built = .done value heap := by
  obtain ⟨result, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, value, heap, done, InternedNestedConstruction.Outcome.state]
private theorem initial (width : Nat) : SourceCurrentConjunctionClassScan.Ready (before width) ∧
    Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  apply SourceCurrentConjunctionClassHistoryEntry.constructed width history Cache.empty_valid expression
    (fun original member => by simpa only [expression, SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards, SourceEqualityConstraintOrigins.childGuards,
      List.nil_append, List.append_nil] using member) value heap constructed
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap, built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedNativeInventoryCold.pairInventory heap (initial 0).1.good.native.machine.1 value value
    (initial 0).2.2.2 (initial 0).2.2.2 (initial 0).2.1 (initial 0).2.1 (initial 0).2.2.1 (initial 0).2.2.1
private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next, heap.edges.next, machine.domains.next, InternedValueMassHeap.initialBound heap⟩
private theorem initial_fits (width : Nat) : Fits profile (before width) :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap (initial width).1.good.native.machine.1⟩

private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance
private def values : List (Value Symbol Guard) := [value, .reference .depth]
private def firstClass : EqualityNormalize.Class := [[0, 0]]
private def skippedClass : EqualityNormalize.Class := [[1]]
private def lastClass : EqualityNormalize.Class := [[7]]
private def classes : EqualityNormalize.Constraints := [firstClass, skippedClass, lastClass]
private def selected : EqualityNormalize.Constraints := [firstClass, lastClass]
private def alphabet : List Guard := [annotation]
private def memo : SourceCurrentEmptinessMemo.Memo := SourceCurrentEmptinessMemo.empty
private theorem available : InternedNestedProvenance.Values heap values := by
  intro candidate member
  rcases List.mem_cons.mp member with rfl | member
  · exact (initial 0).2.1
  · have same := List.mem_singleton.mp member
    cases same
    exact reference_available heap .depth (by
      intro identity impossible
      simp only [Value.free, List.mem_singleton, reduceCtorEq] at impossible)
private theorem forest_open : ¬MergedColdReaderClosedInputs.ClosedValues values := by
  intro closed
  have impossible := closed (.reference .depth) (List.mem_cons_of_mem _ List.mem_cons_self)
  cases impossible
private theorem carrier : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) heap := by
  have allowed : SourceEqualityAnnotationConstruction.Allowed (fun guard : Guard => guard ∈ alphabet) expression := by
    simp only [expression, SourceEqualityAnnotationConstruction.Allowed,
      SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]
    exact ⟨List.mem_cons_self, trivial, trivial⟩
  exact SourceEqualityAnnotationConstruction.build _ expression allowed [] empty
    (SourceEqualityAnnotationHeap.empty_heap _)
private theorem frame (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) : Frame formulas solver inventory (before width) :=
  Frame.initial formulas solver inventory machine operations (initial width).1 guards rfl
private theorem proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [] := by
  intro paths included path member
  simp only [classes, List.mem_cons, List.not_mem_nil, or_false] at included
  rcases included with rfl | rfl | rfl
  all_goals
    have same := List.mem_singleton.mp member
    cases same
    simp only [firstClass, skippedClass, lastClass, ne_eq, List.cons_ne_nil, not_false_eq_true]
private theorem finite_value : ∃ entry edges, value = .node entry edges 0 [] := by
  have depth : value.depth = 0 := by cbv
  have free : value.free = [] := (initial 0).2.2.1
  cases same : value with
  | node entry edges depth' free' =>
      simp only [same, Value.depth] at depth
      simp only [same, Value.free] at free
      exact ⟨entry, edges, by simp only [depth, free]⟩
  | empty | reference | union | mu => cbv at same; cases same
private theorem first_gate : EndpointStatefulGateTrace.ClassTrace SourceMemoGate.unconstrained
    (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values firstClass heap false heap := by
  apply EndpointStatefulGateTrace.ClassTrace.next
  · apply EndpointStatefulGateTrace.PathTrace.child
    apply EndpointStatefulGateTrace.ChildTrace.present (value := value) rfl
    obtain ⟨entry, edges, same⟩ := finite_value
    rw [same]
    exact .finite rfl
  · exact .nil
private theorem primary_skip : EndpointStatefulGateTrace.ClassTrace SourceMemoGate.unconstrained
    (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values skippedClass heap true heap :=
  .stop (.child (.present rfl .reference))
private theorem secondary_skip : SourceCurrentSecondaryTrace.ClassTrace SourceMemoGate.unconstrained
    values skippedClass heap true heap := .stop (.child (.present rfl .reference))
private theorem last_gate : EndpointStatefulGateTrace.ClassTrace SourceMemoGate.unconstrained
    (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values lastClass heap false heap :=
  .next (.child (.missing rfl)) .nil
private theorem expected (width : Nat) : SourceCurrentConjunctionClassScan.Scan 2 SourceMemoGate.unconstrained
    (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values classes (before width) memo
      none selected (before width) memo :=
  .selected first_gate (.skipped primary_skip secondary_skip (.selected last_gate .nil))

/-- Initial source and numeric reservations construct the full Scan with selected/skipped/missing branches and original order. -/
theorem constructed_branches (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (reserved : SourceCurrentScanNumericForecast.Reserved bits 2 values.length classes alphabet profile) :
    ¬MergedColdReaderClosedInputs.ClosedValues values ∧
      ∃ next, SourceCurrentScanNumeric.Receipt formulas solver alphabet profile 2 values classes
        (before (bits + 2)) memo none selected (before (bits + 2)) memo next := by
  obtain ⟨outcome, returnedClasses, after, saved, next, receipt⟩ := SourceCurrentScanNumeric.complete formulas solver
    alphabet 2 values classes (before (bits + 2)) memo inventory (frame _ formulas solver) profile (initial_fits _)
    available (SourceCurrentEmptinessMemo.empty_correct formulas solver heap) carrier proper reserved
    EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap)
  obtain ⟨g, s, p, h, n, stable⟩ := SourceCurrentAllocatedScanWorkerCompletion.scan_complete (expected (bits + 2))
  have literal := stable g s p h n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  let ceiling := SourceCurrentScanNumericForecast.fuel 2 values.length classes alphabet profile
  have computed := receipt.run ceiling ceiling ceiling ceiling ceiling
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨sameResult, sameAfter, sameSaved⟩ := SourceCurrentAllocatedScanWorkerStability.scan_done_unique computed literal
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj sameResult
  cases sameAfter
  cases sameSaved
  exact ⟨forest_open, next, receipt⟩

end MicroCFTA.ScanNumericIntegration

#check @MicroCFTA.ScanNumericIntegration.constructed_branches
#print axioms MicroCFTA.ScanNumericIntegration.constructed_branches
