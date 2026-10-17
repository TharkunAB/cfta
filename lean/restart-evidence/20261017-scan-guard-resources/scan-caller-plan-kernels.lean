import MicroCFTA.SourceCurrentScanCallerNumeric
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.InternedFreshOrdinaryStoredCosts
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

namespace MicroCFTA.ScanCallerPlanKernels
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

private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance

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

private theorem initial_frame (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Frame formulas solver inventory (before (bits + 2)) :=
  Frame.initial formulas solver inventory machine operations (initial (bits + 2)).1 guards rfl

private def values : List (Value Symbol Guard) := [value, value, .reference .depth]
private def classes : EqualityNormalize.Constraints := [[[0], [1]], [[0], [1]]]
private def caller (width : Nat) : SourceCurrentAllocatedPartialState.State width :=
  SourceCurrentAllocatedPartialState.initial (before width)
    SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private theorem available_values (width : Nat) : InternedNestedProvenance.Values heap values := by
  intro child member
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (initial width).2.1
  · exact (initial width).2.1
  · exact InternedNestedProvenance.depth_available _
private theorem proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [] := by
  intro paths member path included
  have same : paths = [[0], [1]] := by
    simpa only [classes, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  subst paths
  simp only [List.mem_cons, List.not_mem_nil, or_false] at included
  rcases included with rfl | rfl <;> decide
private theorem active : ∀ paths ∈ classes, EqualityNormalize.Nontrivial paths := by
  intro paths member
  have same : paths = [[0], [1]] := by
    simpa only [classes, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  subst paths
  exact ⟨[0], by simp, [1], by simp, by decide⟩
private theorem context (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory (caller width) EndpointMemoGateTrace.empty := by
  have frame : Frame formulas solver inventory (before width) :=
    Frame.initial formulas solver inventory machine operations (initial width).1 guards rfl
  exact ⟨(initial width).1, frame.admitted,
    SourceCurrentAllocatedPartialMemoSound.initial_sound formulas solver (before width)
      SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty,
    SourceCurrentMemoMergeEffects.stored_empty heap,
    (fun ambient => SourceCurrentMemoMergeLanguage.cache_covers_empty
      (SourceEqualityPCSGuard.holds formulas solver) ambient),
    SourceCurrentEmptinessMemo.empty_correct formulas solver heap, EndpointMemoGateTrace.empty_valid heap,
    SourceCurrentAllocatedMuRebuild.constructed expression value heap constructed⟩

/-- Two active distinct-path classes construct their own full caller Scan from initial reservations. -/
theorem constructed_active_caller (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (reserved : SourceCurrentScanNumericForecast.Reserved bits 0 values.length classes
      (SourceCurrentConjunctionGuardUniverse.guards heap) profile) :
    (∀ depth, ¬Cap depth value) ∧ ¬MergedColdReaderClosedInputs.ClosedValues values ∧
    ∃ outcome selected after saved next final,
      ∃ receipt : SourceCurrentScanNumeric.Receipt formulas solver
          (SourceCurrentConjunctionGuardUniverse.guards heap) profile 0 values classes
          (before (bits + 2)) SourceCurrentEmptinessMemo.empty outcome selected after saved next,
        SourceCurrentAllocatedScanSourceReads.ScanReads receipt.actual EndpointMemoGateTrace.empty final ∧
        SourceCurrentAllocatedPartialInvariant.Post formulas solver next (caller (bits + 2))
          (SourceCurrentAllocatedPartialState.advance (caller (bits + 2)) after saved SourceCurrentMemoMergeGraph.empty) final ∧
        selected.Sublist classes ∧ SourceCurrentAllocatedScanCaller.StoppedSound formulas solver values classes outcome ∧
        (SourceCurrentAllocatedPartialState.advance (caller (bits + 2)) after saved SourceCurrentMemoMergeGraph.empty).nodeResults =
          (caller (bits + 2)).nodeResults ∧
        (SourceCurrentAllocatedPartialState.advance (caller (bits + 2)) after saved SourceCurrentMemoMergeGraph.empty).edgeResults =
          (caller (bits + 2)).edgeResults ∧
        (SourceCurrentAllocatedPartialState.advance (caller (bits + 2)) after saved SourceCurrentMemoMergeGraph.empty).merge =
          (caller (bits + 2)).merge ∧
        (SourceCurrentAllocatedPartialState.advance (caller (bits + 2)) after saved SourceCurrentMemoMergeGraph.empty).fourth = saved := by
  refine ⟨no_cap, ?_, ?_⟩
  · intro closed
    have impossible := closed (.reference .depth) (by simp [values])
    cases impossible
  · exact SourceCurrentScanCallerNumeric.complete formulas solver inventory 0 values classes
      (caller (bits + 2)) EndpointMemoGateTrace.empty (context _ formulas solver)
      (initial_frame bits formulas solver) profile (initial_fits _) (available_values (bits + 2)) proper active reserved

/-- Empty classes construct an exact unchanged Scan and same-inventory caller without Room. -/
theorem constructed_empty_caller (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ next final,
      ∃ receipt : SourceCurrentScanNumeric.Receipt formulas solver
          (SourceCurrentConjunctionGuardUniverse.guards heap) profile 0 values []
          (before (bits + 2)) SourceCurrentEmptinessMemo.empty none [] (before (bits + 2))
          SourceCurrentEmptinessMemo.empty next,
        SourceCurrentAllocatedScanSourceReads.ScanReads receipt.actual EndpointMemoGateTrace.empty final ∧
        SourceCurrentAllocatedPartialInvariant.Post formulas solver next (caller (bits + 2))
          (SourceCurrentAllocatedPartialState.advance (caller (bits + 2)) (before (bits + 2))
            SourceCurrentEmptinessMemo.empty SourceCurrentMemoMergeGraph.empty) final ∧
        Frame formulas solver next (before (bits + 2)) ∧
        SourceCurrentAllocatedScanWorker.scan 0 0 0 0 0 0 values [] (before (bits + 2)) SourceCurrentEmptinessMemo.empty =
          .done (none, []) (before (bits + 2)) SourceCurrentEmptinessMemo.empty := by
  obtain ⟨outcome, selected, after, saved, next, final, receipt, reads, post, _sublist, _sound, _tables⟩ :=
    SourceCurrentScanCallerNumeric.complete formulas solver inventory 0 values []
      (caller (bits + 2)) EndpointMemoGateTrace.empty (context _ formulas solver)
      (initial_frame bits formulas solver) profile (initial_fits _) (available_values (bits + 2))
      (by intro paths member; cases member) (by intro paths member; cases member) trivial
  have actual := receipt.actual
  cases actual
  exact ⟨next, final, receipt, reads, post, receipt.frame, rfl⟩

end MicroCFTA.ScanCallerPlanKernels

#print axioms MicroCFTA.ScanCallerPlanKernels.constructed_active_caller
#check @MicroCFTA.ScanCallerPlanKernels.constructed_active_caller
#print MicroCFTA.ScanCallerPlanKernels.constructed_active_caller

#print axioms MicroCFTA.ScanCallerPlanKernels.constructed_empty_caller
#check @MicroCFTA.ScanCallerPlanKernels.constructed_empty_caller
#print MicroCFTA.ScanCallerPlanKernels.constructed_empty_caller
