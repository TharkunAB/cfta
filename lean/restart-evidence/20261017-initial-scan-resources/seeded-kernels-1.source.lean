import MicroCFTA.SourceCurrentConstrainedCapSeededNumeric
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

namespace MicroCFTA.SeededNumericKernels
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

private theorem initial_frame (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Frame formulas solver inventory (before (bits + 2)) :=
  Frame.initial formulas solver inventory machine operations (initial (bits + 2)).1 guards rfl
private def values : List (Value Symbol Guard) := [value, .reference .depth]
private def paths : List (List Int) := [[0], [0]]
private theorem available_values (width : Nat) : InternedNestedProvenance.Values (before width).native.machine.heap values := by
  intro child member
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact (initial width).2.1
  · exact InternedNestedProvenance.depth_available _
private theorem supported : ∀ path ∈ paths, SourceCurrentSecondaryProjectionScoped.PathSupport (fun _ => false) heap path values := by
  intro path member
  have same : path = [0] := by simpa only [paths, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  subst path
  refine ⟨[0], rfl, ?_⟩
  intro child found
  have same : child = value := (Option.some.inj found).symm
  subst child
  exact Or.inl (initial 0).2.2.1
private theorem proper : ∀ path ∈ paths, path ≠ [] := by
  intro path member
  have same : path = [0] := by simpa only [paths, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  rw [same]
  decide

/-- Two selected projections construct their own checked query despite an open sibling and an uncapped selected Mu. -/
theorem constructed_selected_uncapped (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      (SourceCurrentConstrainedCapSeededForecast.finalProfile values.length paths profile)) :
    (∀ depth, ¬Cap depth value) ∧ ¬MergedColdReaderClosedInputs.ClosedValues values ∧
    ∃ result after next final, ∃ actual : SourceCurrentAllocatedSeededQuery.Seeded values paths (before (bits + 2)) result after,
      SourceCurrentAllocatedSeededMemos.SeededReads actual EndpointMemoGateTrace.empty final ∧
      SourceCurrentConstrainedCapSeededNumeric.Receipt formulas solver next (before (bits + 2)) result after
        EndpointMemoGateTrace.empty final ∧
      Fits (SourceCurrentConstrainedCapSeededForecast.finalProfile values.length paths profile) after ∧
      (paths ≠ [] → SourceCurrentAllocatedSeededLanguage.Includes formulas solver values paths result) ∧
      SourceCurrentAllocatedSeededWorker.seeded
        (SourceCurrentConstrainedCapSeededForecast.fuel values.length paths profile)
        (SourceCurrentConstrainedCapSeededForecast.fuel values.length paths profile)
        (SourceCurrentConstrainedCapSeededForecast.fuel values.length paths profile)
        values paths (before (bits + 2)) = .done result after := by
  refine ⟨no_cap, ?_, ?_⟩
  · intro closed
    have impossible := closed (.reference .depth) (List.mem_cons_of_mem _ List.mem_cons_self)
    cases impossible
  · exact SourceCurrentConstrainedCapSeededNumeric.complete formulas solver inventory (fun _ => false) heap
      (initial (bits + 2)).1.semantic
      (SourceCurrentClassGateCompletion.gate_ready (initial (bits + 2)).1.semantic (initial (bits + 2)).1.costs)
      values paths (before (bits + 2)) profile (initial_frame bits formulas solver) (initial_fits _) (available_values _)
      (grows_refl _) supported proper
      (SourceCurrentConstrainedCapSeededForecast.reserved_of_final_room bits values.length [0] [[0]] profile room)
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid _)

/-- No paths need no room, and the open unresolved sibling is never projected. -/
theorem constructed_empty_seed (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ result after next final, ∃ actual : SourceCurrentAllocatedSeededQuery.Seeded values [] (before (bits + 2)) result after,
      SourceCurrentAllocatedSeededMemos.SeededReads actual EndpointMemoGateTrace.empty final ∧
      SourceCurrentConstrainedCapSeededNumeric.Receipt formulas solver next (before (bits + 2)) result after
        EndpointMemoGateTrace.empty final ∧ Fits profile after ∧
      ([] ≠ [] → SourceCurrentAllocatedSeededLanguage.Includes formulas solver values [] result) ∧
      SourceCurrentAllocatedSeededWorker.seeded 0 0 0 values [] (before (bits + 2)) = .done result after := by
  exact SourceCurrentConstrainedCapSeededNumeric.complete formulas solver inventory (fun _ => false) heap
    (initial (bits + 2)).1.semantic
    (SourceCurrentClassGateCompletion.gate_ready (initial (bits + 2)).1.semantic (initial (bits + 2)).1.costs)
    values [] (before (bits + 2)) profile (initial_frame bits formulas solver) (initial_fits _) (available_values _)
    (grows_refl _) (by intro path member; cases member) (by intro path member; cases member) trivial
    EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid _)

end MicroCFTA.SeededNumericKernels
#print axioms MicroCFTA.SeededNumericKernels.constructed_selected_uncapped
#check @MicroCFTA.SeededNumericKernels.constructed_selected_uncapped
#print MicroCFTA.SeededNumericKernels.constructed_selected_uncapped
#print axioms MicroCFTA.SeededNumericKernels.constructed_empty_seed
#check @MicroCFTA.SeededNumericKernels.constructed_empty_seed
#print MicroCFTA.SeededNumericKernels.constructed_empty_seed
