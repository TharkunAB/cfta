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

namespace MicroCFTA.AdapterIntegration
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
private def naturalPaths : EqualityNormalize.Class := [[0], [0]]
private def caller (width : Nat) : SourceCurrentAllocatedPartialState.State width :=
  SourceCurrentAllocatedPartialState.initial (before width) SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty

private theorem values_available : InternedNestedProvenance.Values heap values := by
  intro candidate member
  rcases List.mem_cons.mp member with rfl | member
  · exact (initial 0).2.1
  · have same : candidate = .reference .depth := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
    cases same
    exact InternedProbeProvenance.reference_available heap .depth (by intro identity impossible; simp only [Value.free, List.mem_singleton, reduceCtorEq] at impossible)

private theorem not_all_closed : ¬MergedColdReaderClosedInputs.ClosedValues values := by
  intro closed
  have impossible := closed (.reference .depth) (by simp only [values, List.mem_cons, List.not_mem_nil, or_false, or_true])
  cases impossible

private theorem selected_support : ∀ path ∈ paths,
    SourceCurrentSecondaryProjectionScoped.PathSupport SourceMemoGate.unconstrained heap path values := by
  intro path member
  have same : path = [0] := by simpa only [paths, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  cases same
  refine ⟨[0], rfl, ?_⟩
  intro candidate found
  have same : value = candidate := Option.some.inj found
  cases same
  exact Or.inl (initial 0).2.2.1

private theorem proper : ∀ path ∈ paths, path ≠ [] := by
  intro path member
  have same : path = [0] := by simpa only [paths, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  simp only [same, ne_eq, List.cons_ne_nil, not_false_eq_true]

private theorem initial_frame (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) : Frame formulas solver inventory (before width) :=
  Frame.initial formulas solver inventory machine operations (initial width).1 guards rfl

private theorem initial_context (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory (caller width) EndpointMemoGateTrace.empty := by
  refine ⟨(initial width).1, (initial_frame width formulas solver).admitted,
    SourceCurrentAllocatedPartialMemoSound.initial_sound formulas solver _ _ _,
    SourceCurrentMemoMergeEffects.stored_empty _, ?_,
    SourceCurrentEmptinessMemo.empty_correct formulas solver heap, EndpointMemoGateTrace.empty_valid heap, ?_⟩
  · intro ambient key entry absent
    cases absent
  · change InternedFreshOrdinaryProbeHeap.Heap heap
    simpa only [heap, built] using InternedFreshOrdinaryProbeHeap.closed_heap expression

/-- Initial source facts construct the full supported caller beside an unselected open reference. -/
theorem constructed_caller (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (reserved : SourceCurrentConstrainedCapSeededForecast.SeededReserved bits values.length paths profile) :
    (∀ depth, ¬Cap depth value) ∧ ¬MergedColdReaderClosedInputs.ClosedValues values ∧
    ∃ result after next final,
      SourceCurrentAllocatedPartialInvariant.Post formulas solver next (caller (bits + 2))
        (SourceCurrentAllocatedPartialState.advance (caller (bits + 2)) after
          (caller (bits + 2)).fourth (caller (bits + 2)).merge) final ∧
      Frame formulas solver next after ∧
      Fits (SourceCurrentConstrainedCapSeededForecast.finalProfile values.length paths profile) after ∧
      SourceCurrentAllocatedSeededLanguage.Includes formulas solver values paths result ∧ result.free = [] ∧
      (SourceCurrentAllocatedPartialState.advance (caller (bits + 2)) after
        (caller (bits + 2)).fourth (caller (bits + 2)).merge).nodeResults = (caller (bits + 2)).nodeResults ∧
      (SourceCurrentAllocatedPartialState.advance (caller (bits + 2)) after
        (caller (bits + 2)).fourth (caller (bits + 2)).merge).edgeResults = (caller (bits + 2)).edgeResults ∧
      (SourceCurrentAllocatedPartialState.advance (caller (bits + 2)) after
        (caller (bits + 2)).fourth (caller (bits + 2)).merge).fourth = (caller (bits + 2)).fourth ∧
      (SourceCurrentAllocatedPartialState.advance (caller (bits + 2)) after
        (caller (bits + 2)).fourth (caller (bits + 2)).merge).merge = (caller (bits + 2)).merge ∧
      SourceCurrentAllocatedSeededWorker.seeded
        (SourceCurrentConstrainedCapSeededForecast.fuel values.length paths profile)
        (SourceCurrentConstrainedCapSeededForecast.fuel values.length paths profile)
        (SourceCurrentConstrainedCapSeededForecast.fuel values.length paths profile)
        values paths (before (bits + 2)) = .done result after ∧
      (∀ projection reader native, SourceCurrentConstrainedCapSeededForecast.fuel values.length paths profile ≤ projection →
        SourceCurrentConstrainedCapSeededForecast.fuel values.length paths profile ≤ reader →
        SourceCurrentConstrainedCapSeededForecast.fuel values.length paths profile ≤ native →
        SourceCurrentAllocatedSeededWorker.seeded projection reader native values paths (before (bits + 2)) = .done result after) := by
  have ready := (initial (bits + 2)).1
  obtain ⟨result, after, next, final, actual, reads, receipt, post, fits, included,
      nodes, edges, fourth, merge, done, stable⟩ :=
    SourceCurrentSeededCallerNumeric.complete formulas solver inventory SourceMemoGate.unconstrained heap
      ready.semantic (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs)
      values paths (caller (bits + 2)) EndpointMemoGateTrace.empty (initial_context _ formulas solver)
      (initial_frame _ formulas solver) profile (initial_fits _) values_available (grows_refl heap)
      selected_support proper reserved
  exact ⟨no_cap, not_all_closed, result, after, next, final, post, receipt.frame, fits,
    included (by simp only [paths, ne_eq, List.cons_ne_nil, not_false_eq_true]), receipt.closed,
    nodes, edges, fourth, merge, done, stable⟩

/-- Both gate modes construct their own ordered returns and retain the full Frame at each heap. -/
theorem constructed_gate_chain (width : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ primaryAnswer primaryHeap secondaryAnswer secondaryHeap,
      EndpointStatefulGateTrace.ClassTrace SourceMemoGate.unconstrained (fun _ => false)
        values naturalPaths heap primaryAnswer primaryHeap ∧
      SourceCurrentSecondaryTrace.ClassTrace SourceMemoGate.unconstrained
        values naturalPaths primaryHeap secondaryAnswer secondaryHeap ∧
      Frame formulas solver inventory (SourceCurrentConjunctionClassScan.advanceHeap
        (SourceCurrentConjunctionClassScan.advanceHeap (before width) primaryHeap) secondaryHeap) ∧
      Fits (SourceCurrentGateFrameResources.forecast naturalPaths
        (SourceCurrentGateFrameResources.forecast naturalPaths profile))
        (SourceCurrentConjunctionClassScan.advanceHeap
          (SourceCurrentConjunctionClassScan.advanceHeap (before width) primaryHeap) secondaryHeap) ∧
      (∀ fuel, SourceCurrentGateFrameResources.workerFuel naturalPaths profile ≤ fuel →
        SourceCurrentMuEndpoint.classMeets true SourceMemoGate.unconstrained (fun _ => false)
          fuel values naturalPaths heap = .done (some primaryAnswer) primaryHeap) ∧
      (∀ fuel, SourceCurrentGateFrameResources.workerFuel naturalPaths
          (SourceCurrentGateFrameResources.forecast naturalPaths profile) ≤ fuel →
        SourceCurrentMuEndpoint.classMeets false SourceMemoGate.unconstrained (fun _ => false)
          fuel values naturalPaths primaryHeap = .done (some secondaryAnswer) secondaryHeap) := by
  obtain ⟨firstAnswer, firstHeap, first, middleFrame, middleFits, retained, _effects, firstDone⟩ :=
    SourceCurrentGateFrameResources.primary formulas solver inventory SourceMemoGate.unconstrained (fun _ => false)
      values naturalPaths (before width) (initial_frame width formulas solver) profile (initial_fits width) values_available
  obtain ⟨lastAnswer, lastHeap, last, finalFrame, finalFits, _retained, _effects, lastDone⟩ :=
    SourceCurrentGateFrameResources.secondary formulas solver inventory SourceMemoGate.unconstrained (fun _ => false)
      values naturalPaths (SourceCurrentConjunctionClassScan.advanceHeap (before width) firstHeap) middleFrame
      (SourceCurrentGateFrameResources.forecast naturalPaths profile) middleFits retained
  exact ⟨firstAnswer, firstHeap, lastAnswer, lastHeap, first, last, finalFrame, finalFits, firstDone, lastDone⟩

end MicroCFTA.AdapterIntegration

#check @MicroCFTA.AdapterIntegration.constructed_caller
#print axioms MicroCFTA.AdapterIntegration.constructed_caller
#print MicroCFTA.AdapterIntegration.constructed_caller
#check @MicroCFTA.AdapterIntegration.constructed_gate_chain
#print axioms MicroCFTA.AdapterIntegration.constructed_gate_chain
#print MicroCFTA.AdapterIntegration.constructed_gate_chain
