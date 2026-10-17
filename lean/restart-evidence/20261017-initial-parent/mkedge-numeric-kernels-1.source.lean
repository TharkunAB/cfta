import MicroCFTA.SourceCurrentMkEdgeNumeric
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

namespace MicroCFTA.MkEdgeNumericIntegration
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
  .binder false (.node [.mk ("pair", .top) annotation [.var 0, .var 0]])
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

private theorem no_cap (depth : Nat) : ¬Cap depth value := by
  intro bounded
  cbv at bounded
  cases bounded with
  | plain _ annotated =>
      cases annotated with
      | mu _ _ _ _ body =>
          cases body with
          | node _ _ _ _ annotations _ =>
              have rejected := annotations _ List.mem_cons_self
              change SourceMemoGate.plain annotation = true at rejected
              have invalid : SourceMemoGate.plain annotation = false := by cbv
              rw [invalid] at rejected
              cases rejected

private def inputs : List (Value Symbol Guard) := [value, value, .reference .depth]
private def constraint : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula := ⟨field, .top⟩
private def symbol : Symbol := ("new-parent", .top)
private theorem readback : SourceEqualityConjoinAllocation.readback constraint = annotation := by cbv
private theorem input_available : InternedNestedProvenance.Values heap inputs := by
  intro child member
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (initial 0).2.1
  · exact (initial 0).2.1
  · exact InternedNestedProvenance.depth_available _
private theorem open_inputs : ¬MergedColdReaderClosedInputs.ClosedValues inputs := by
  intro closed
  have impossible := closed (.reference .depth) (by simp [inputs])
  cases impossible
private theorem initial_frame (width : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Frame formulas solver inventory (before width) :=
  Frame.initial formulas solver inventory machine operations (initial width).1 guards rfl
private theorem stored_ready : SourceEqualityConstraintAllocation.Ready operations.constraints field := by
  obtain ⟨actual, final, done, _, ready, _, _, _⟩ := SourceEqualityConstraintAllocation.construct_complete
    annotation.equalities cached Cache.emptyState Cache.empty_valid
  have same := Prod.mk.inj (done.symm.trans allocation)
  have sameField := Except.ok.inj same.1
  cases sameField
  cases same.2
  exact ready
private theorem field_available : SourceCurrentConjunctionEquality.FieldAvailable operations annotation :=
  SourceCurrentConjunctionFieldAllocation.of_receipt operations annotation cached field stored_ready (by cbv)

/-- Actual original fields retain open uncapped children at the initial constructor forecast. -/
theorem constructed_kept (width : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth value) ∧ ¬MergedColdReaderClosedInputs.ClosedValues inputs ∧
    ∃ result after,
      SourceCurrentAllocatedMkEdge.Receipt formulas solver inventory symbol constraint inputs (before width) result after ∧
      Frame formulas solver inventory after ∧ Fits (SourceCurrentMkEdgeNumeric.finalProfile inputs.length profile) after ∧
      result.children = inputs ∧ result.entry.key.constraint = annotation ∧
      after.native.machine.heap.nodes.next = heap.nodes.next ∧ after.native.machine.heap.edges.next ≤ heap.edges.next + 1 := by
  have fieldAvailable : SourceCurrentConjunctionEquality.FieldAvailable operations
      (SourceEqualityConjoinAllocation.readback constraint) := readback ▸ field_available
  obtain ⟨result, after, receipt, frame, fits, nodes, edges⟩ := SourceCurrentMkEdgeNumeric.complete
    formulas solver inventory symbol constraint inputs (before width) (initial_frame width formulas solver) profile (initial_fits width)
    stored_ready fieldAvailable input_available
  have kept : SourceEqualityMkEdgeAllocation.accepted annotation inputs.length = true := by cbv
  refine ⟨no_cap, open_inputs, result, after, receipt, frame, fits, ?_, ?_, nodes, edges⟩
  · simpa only [readback, kept, ↓reduceIte] using receipt.children
  · simpa only [readback, kept, ↓reduceIte] using receipt.guard

/-- An actual arity rejection keeps the full state and derives the literal empty sentinel. -/
theorem constructed_arity_sentinel (width : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ result after,
      SourceCurrentAllocatedMkEdge.Receipt formulas solver inventory symbol constraint [value] (before width) result after ∧
      Frame formulas solver inventory after ∧ Fits (SourceCurrentMkEdgeNumeric.finalProfile 1 profile) after ∧
      result.children = [.empty] ∧ result.entry.key.constraint = SourceEqualityConstraintConstructors.top ∧
      ∀ holds ambient term, ¬InternedGuardedLanguage.edgeMeaning holds ambient result term := by
  have fieldAvailable : SourceCurrentConjunctionEquality.FieldAvailable operations
      (SourceEqualityConjoinAllocation.readback constraint) := readback ▸ field_available
  have available : InternedNestedProvenance.Values heap ([value] : List (Value Symbol Guard)) := by
    intro child member
    cases List.mem_singleton.mp member
    exact (initial width).2.1
  obtain ⟨result, after, receipt, frame, fits, _nodes, _edges⟩ := SourceCurrentMkEdgeNumeric.complete
    formulas solver inventory symbol constraint [value] (before width) (initial_frame width formulas solver) profile (initial_fits width)
    stored_ready fieldAvailable available
  have rejected : SourceEqualityMkEdgeAllocation.accepted annotation 1 = false := by cbv
  have children : result.children = [.empty] := by
    simpa only [readback, rejected, Bool.false_eq_true, ↓reduceIte] using receipt.children
  refine ⟨result, after, receipt, frame, fits, children, ?_, ?_⟩
  · simpa only [readback, rejected, Bool.false_eq_true, ↓reduceIte] using receipt.guard
  · exact SourceEqualityNativeDemandMismatchProvenance.empty_child_rejects result children

/-- Raw contradiction has no child or field demand and repeats at the exact first returned state. -/
theorem constructed_raw_reject (width : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    let actual := SourceCurrentAllocatedMkEdge.reject symbol (before width)
    SourceCurrentAllocatedMkEdge.RejectReceipt formulas solver inventory symbol (before width) actual.1 actual.2 ∧
      Frame formulas solver inventory actual.2 ∧ Fits (SourceCurrentMkEdgeNumeric.finalProfile 0 profile) actual.2 ∧
      (∀ children : List (Value Symbol Guard), SourceCurrentAllocatedMkEdge.build symbol ⟨.contradiction, .top⟩ children
        (before width) = (.ok actual.1, actual.2)) ∧
      SourceCurrentAllocatedMkEdge.reject symbol actual.2 = (actual.1, actual.2) ∧
      ∀ holds ambient term, ¬InternedGuardedLanguage.edgeMeaning holds ambient actual.1 term := by
  obtain ⟨receipt, frame, fits, _nodes, _edges⟩ := SourceCurrentMkEdgeNumeric.reject
    formulas solver inventory symbol (before width) (initial_frame width formulas solver) profile (initial_fits width)
  refine ⟨receipt, frame, fits, ?_, ?_, receipt.empty⟩
  · intro children
    exact SourceCurrentAllocatedMkEdge.build_contradictory symbol ⟨.contradiction, .top⟩ children (before width) rfl
  · cbv

end MicroCFTA.MkEdgeNumericIntegration

#check @MicroCFTA.MkEdgeNumericIntegration.constructed_kept
#print axioms MicroCFTA.MkEdgeNumericIntegration.constructed_kept
#check @MicroCFTA.MkEdgeNumericIntegration.constructed_arity_sentinel
#print axioms MicroCFTA.MkEdgeNumericIntegration.constructed_arity_sentinel
#check @MicroCFTA.MkEdgeNumericIntegration.constructed_raw_reject
#print axioms MicroCFTA.MkEdgeNumericIntegration.constructed_raw_reject
