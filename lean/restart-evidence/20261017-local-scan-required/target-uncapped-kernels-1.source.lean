import MicroCFTA.SourceCurrentTargetNumeric
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

namespace MicroCFTA.UncappedTargetIntegration
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

private def values : List (Value Symbol Guard) := [value, .reference .depth]
private def paths : List (List Int) := [[0], [0]]
private theorem available : InternedNestedProvenance.Values heap values := by
  intro original member
  rcases List.mem_cons.mp member with rfl | member
  · exact (initial 0).2.1
  · exact List.mem_singleton.mp member ▸ InternedNestedProvenance.depth_available _
private theorem selected : ∀ path ∈ paths, SourceEqualityProjectionPathDomain.ForestClosed path values := by
  intro path member
  have same : path = [0] := by simpa only [paths, List.mem_cons, List.mem_singleton, or_self] using member
  subst path
  simpa only [SourceEqualityProjectionPathDomain.ForestClosed, values,
    SourceEqualityProjectionPathDomain.NodeClosed, SourceEqualityProjectionGraph.select] using (initial 0).2.2.1
private theorem empty_covered (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient
      (SourceCurrentMemoMergeGraph.empty : SourceCurrentMemoMergeGraph.Memo Symbol Guard) := by
  intro ambient key entry absent
  cases absent

/-- A source-built constrained Mu outside every Cap enters the complete duplicate-path Target beside an open root. -/
theorem constructed_uncapped_target (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (reserved : SourceCurrentConstrainedCapTargetForecast.TargetReserved bits values.length paths profile) :
    (∀ depth, ¬Cap depth value) ∧ ¬MergedColdReaderClosedInputs.ClosedValues values ∧
      ∃ next result after saved final,
        ∃ actual : SourceCurrentAllocatedTargetGraph.Target values paths (before (bits + 2))
            SourceCurrentMemoMergeGraph.empty result after saved,
          SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual EndpointMemoGateTrace.empty final ∧
          SourceCurrentAllocatedTargetComplete.Receipt formulas solver next values paths (before (bits + 2))
            SourceCurrentMemoMergeGraph.empty result after saved EndpointMemoGateTrace.empty final ∧
          Frame formulas solver next after ∧
          Fits (SourceCurrentConstrainedCapTargetForecast.targetProfile values.length paths profile) after ∧
          ∀ query projection reader merge selection,
            SourceCurrentConstrainedCapTargetForecast.targetFuel values.length paths profile ≤ query →
            SourceCurrentConstrainedCapTargetForecast.targetFuel values.length paths profile ≤ projection →
            SourceCurrentConstrainedCapTargetForecast.targetFuel values.length paths profile ≤ reader →
            SourceCurrentConstrainedCapTargetForecast.targetFuel values.length paths profile ≤ merge →
            SourceCurrentConstrainedCapTargetForecast.targetFuel values.length paths profile ≤ selection →
            SourceCurrentAllocatedTargetWorker.target query projection reader merge selection values paths
              (before (bits + 2)) SourceCurrentMemoMergeGraph.empty = .done result after saved := by
  have frame := Frame.initial formulas solver inventory machine operations (initial (bits + 2)).1 guards rfl
  obtain ⟨next, result, after, saved, final, actual, reads, receipt, returned, fits, done⟩ :=
    SourceCurrentTargetNumeric.complete formulas solver inventory values paths (before (bits + 2))
      SourceCurrentMemoMergeGraph.empty profile frame (initial_fits _) available selected
      (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid _) reserved
  refine ⟨no_cap, ?_, next, result, after, saved, final, actual, reads, receipt, returned, fits, ?_⟩
  · intro impossible
    have bad := impossible (.reference .depth) (by simp only [values, List.mem_cons, List.mem_singleton, or_true])
    cases bad
  · intro query projection reader merge selection queryEnough projectionEnough readerEnough mergeEnough selectionEnough
    exact SourceCurrentAllocatedTargetWorkerCompletion.target_done_stable done
      queryEnough projectionEnough readerEnough mergeEnough selectionEnough

/-- The same non-Cap source permits an empty Target without any numeric room premise. -/
theorem constructed_empty_target (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ actual : SourceCurrentAllocatedTargetGraph.Target values [] (before (bits + 2))
        SourceCurrentMemoMergeGraph.empty .empty (before (bits + 2)) SourceCurrentMemoMergeGraph.empty,
      SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual EndpointMemoGateTrace.empty EndpointMemoGateTrace.empty ∧
      SourceCurrentAllocatedTargetComplete.Receipt formulas solver inventory values [] (before (bits + 2))
        SourceCurrentMemoMergeGraph.empty .empty (before (bits + 2)) SourceCurrentMemoMergeGraph.empty
        EndpointMemoGateTrace.empty EndpointMemoGateTrace.empty ∧
      SourceCurrentAllocatedTargetWorker.target 0 0 0 0 0 values [] (before (bits + 2))
        SourceCurrentMemoMergeGraph.empty = .done .empty (before (bits + 2)) SourceCurrentMemoMergeGraph.empty := by
  have frame := Frame.initial formulas solver inventory machine operations (initial (bits + 2)).1 guards rfl
  exact ⟨.nil, .nil, SourceCurrentConstrainedCapTargetReceiptComposition.empty frame.ready frame.admitted
    available (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
    (EndpointMemoGateTrace.empty_valid _), rfl⟩

end MicroCFTA.UncappedTargetIntegration

#check @MicroCFTA.UncappedTargetIntegration.constructed_uncapped_target
#print axioms MicroCFTA.UncappedTargetIntegration.constructed_uncapped_target
#check @MicroCFTA.UncappedTargetIntegration.constructed_empty_target
#print axioms MicroCFTA.UncappedTargetIntegration.constructed_empty_target
