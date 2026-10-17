import MicroCFTA.SourceCurrentInheritedNumeric
import MicroCFTA.SourceCurrentAllocatedLocalWorkerStability
import MicroCFTA.SourceCurrentAllocatedClassEditPlan
import MicroCFTA.SourceCurrentConjunctionRequiredActual
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
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 1000000

namespace MicroCFTA.InheritedNumericKernels
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

private def annotation : Guard := ⟨some [[[0, 0], [0, 1]]], .top⟩
private def expression : Syntax Symbol Guard :=
  .node [.mk ("roots", .top) annotation [
    .node [.mk ("finite", .top) annotation [.node [.mk ("left", .top) annotation []], .node [.mk ("right", .top) annotation []]]],
    .binder false (.node [.mk ("pair", .top) annotation [.var 0, .var 0]])]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def finite : Value Symbol Guard := ((children value)[0]?).getD .empty
private def recursive : Value Symbol Guard := ((children value)[1]?).getD .empty
private def allocated := SourceEqualityConstraintAllocation.construct annotation.equalities Cache.emptyState
private def field : SourceEqualityConstraintAllocation.Value := match allocated.1 with
  | .ok value => value
  | .error _ => .contradiction
private def emptyOriginal : Guard := ⟨some [], .top⟩
private def allocatedEmpty := SourceEqualityConstraintAllocation.construct emptyOriginal.equalities allocated.2
private def emptyField : SourceEqualityConstraintAllocation.Value := match allocatedEmpty.1 with
  | .ok own => own
  | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial allocatedEmpty.2
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def before (width : Nat) : Checked width := ⟨initial width machine, operations⟩

private theorem cached : SourceEqualityGuardReadback.Cached annotation.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0, 0], [0, 1]]] = .normalized [[[0, 0], [0, 1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem allocation : allocated = (.ok field, allocated.2) := by cbv
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocatedEmpty.2 [annotation, emptyOriginal] := by
  have first : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocated.2 [annotation] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) cached allocation
  have last : allocatedEmpty = (.ok emptyField, allocatedEmpty.2) := by cbv
  exact SourceEqualityOriginalAllocationHistory.History.construct first SourceEqualityGuardReadback.empty_cached last
private theorem constructed : built = .done value heap := by
  obtain ⟨result, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, value, heap, done, InternedNestedConstruction.Outcome.state]
private theorem initial (width : Nat) : SourceCurrentConjunctionClassScan.Ready (before width) ∧
    Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  apply SourceCurrentConjunctionClassHistoryEntry.constructed width history Cache.empty_valid expression
    (fun original member => by
      have same : original = annotation := by simpa [expression, SourceEqualityConstraintOrigins.guards,
        SourceEqualityConstraintOrigins.edgeGuards, SourceEqualityConstraintOrigins.childGuards] using member
      subst original
      exact List.mem_cons_self) value heap constructed
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap, built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedNativeInventoryCold.pairInventory heap (initial 0).1.good.native.machine.1 value value
    (initial 0).2.2.2 (initial 0).2.2.2 (initial 0).2.1 (initial 0).2.1 (initial 0).2.2.1 (initial 0).2.2.1
private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next, heap.edges.next, machine.domains.next, InternedValueMassHeap.initialBound heap⟩
private theorem initial_fits (width : Nat) : Fits profile (before width) :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap (initial width).1.good.native.machine.1⟩

private theorem no_cap (depth : Nat) : ¬Cap depth recursive := by
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

private def values : List (Value Symbol Guard) := [finite, recursive, .reference .depth]
private def caller (width : Nat) : SourceCurrentAllocatedPartialState.State width :=
  SourceCurrentAllocatedPartialState.initial (before width)
    SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private theorem available_values (width : Nat) : InternedNestedProvenance.Values heap values := by
  intro child member
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (initial width).2.1.children finite (by cbv; exact .head _)
  · exact (initial width).2.1.children recursive (by cbv; exact .tail _ (.head _))
  · exact InternedNestedProvenance.depth_available _
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
private theorem open_values : ¬MergedColdReaderClosedInputs.ClosedValues values := by
  intro closed
  have impossible := closed (.reference .depth) (by simp [values])
  cases impossible
private theorem no_forest_cap : ∀ depth, ¬(∀ child ∈ values, Cap depth child) := by
  intro depth bounded
  exact no_cap depth (bounded recursive (by simp [values]))

private def row : EdgeValue Symbol Guard := (InternedEdgeResidency.nodeEdges value).head (by
  intro absent
  have count : (InternedEdgeResidency.nodeEdges value).length = 1 := by cbv
  have never : (1 : Nat) = 0 := count.symm.trans (congrArg List.length absent)
  cases never)
private theorem row_resident : InternedEdgeResidency.EdgeResident heap row :=
  InternedEdgeResidency.resident_edges heap (initial 0).1.good.native.machine.1.linked value (initial 0).2.1.resident
    row (List.head_mem _)
private theorem empty_ready : SourceEqualityConstraintAllocation.Ready operations.constraints emptyField :=
  (SourceEqualityConstraintFieldLookup.load_ready emptyOriginal operations.constraints
    (initial 0).1.good.operations.constraints SourceEqualityGuardReadback.empty_cached
    (⟨emptyField, .top⟩ : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula) (by cbv)).1
private theorem field_ready : SourceEqualityConstraintAllocation.Ready operations.constraints field :=
  (SourceEqualityConstraintFieldLookup.load_ready annotation operations.constraints
    (initial 0).1.good.operations.constraints cached
    (⟨field, .top⟩ : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula) (by cbv)).1

/-- Own inherited combination feeds its exact combined value into an actual indexed descent. -/
theorem constructed_prefix_descent (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth recursive) ∧
    ∃ combined,
      SourceCurrentAllocatedInheritedPrefix.Receipt formulas solver inventory row.entry.key.constraint emptyField (before (bits + 2)) combined ∧
      SourceCurrentAllocatedPartialDescent.Receipt formulas solver inventory
        (SourceCurrentAllocatedPartialGraph.prefixState (caller (bits + 2)) row emptyField) combined 0 ∧
      Frame formulas solver inventory
        (SourceCurrentAllocatedPartialGraph.descend (SourceCurrentAllocatedPartialGraph.prefixState (caller (bits + 2)) row emptyField) combined 0).2.checked ∧
      Fits profile
        (SourceCurrentAllocatedPartialGraph.descend (SourceCurrentAllocatedPartialGraph.prefixState (caller (bits + 2)) row emptyField) combined 0).2.checked ∧
      SourceCurrentAllocatedPartialInvariant.Post formulas solver inventory (caller (bits + 2))
        (SourceCurrentAllocatedPartialGraph.descend (SourceCurrentAllocatedPartialGraph.prefixState (caller (bits + 2)) row emptyField) combined 0).2
        EndpointMemoGateTrace.empty ∧
      (SourceCurrentAllocatedPartialGraph.descend (SourceCurrentAllocatedPartialGraph.prefixState (caller (bits + 2)) row emptyField) combined 0).2.checked.native =
        (before (bits + 2)).native := by
  obtain ⟨combined, receipt, child, frame, fits, post⟩ := SourceCurrentInheritedNumeric.prefix_descent formulas solver inventory
    row emptyField 0 (caller (bits + 2)) EndpointMemoGateTrace.empty (context _ formulas solver)
    (initial_frame bits formulas solver) profile (initial_fits _) (fun _ => row_resident) (fun _ => empty_ready)
  exact ⟨no_cap, combined, receipt, child, frame, fits, post, rfl⟩

/-- Contradiction skips every field and resident-edge fact and leaves the full caller unchanged. -/
theorem constructed_contradiction (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (edge : EdgeValue Symbol Guard) (index : Nat) :
    ∃ combined,
      SourceCurrentAllocatedInheritedPrefix.Receipt formulas solver inventory edge.entry.key.constraint .contradiction (before (bits + 2)) combined ∧
      SourceCurrentAllocatedPartialDescent.Receipt formulas solver inventory
        (SourceCurrentAllocatedPartialGraph.prefixState (caller (bits + 2)) edge .contradiction) combined index ∧
      Frame formulas solver inventory
        (SourceCurrentAllocatedPartialGraph.descend (SourceCurrentAllocatedPartialGraph.prefixState (caller (bits + 2)) edge .contradiction) combined index).2.checked ∧
      Fits profile
        (SourceCurrentAllocatedPartialGraph.descend (SourceCurrentAllocatedPartialGraph.prefixState (caller (bits + 2)) edge .contradiction) combined index).2.checked ∧
      SourceCurrentAllocatedPartialInvariant.Post formulas solver inventory (caller (bits + 2))
        (SourceCurrentAllocatedPartialGraph.descend (SourceCurrentAllocatedPartialGraph.prefixState (caller (bits + 2)) edge .contradiction) combined index).2
        EndpointMemoGateTrace.empty ∧ combined = .contradiction ∧
      (SourceCurrentAllocatedPartialGraph.descend (SourceCurrentAllocatedPartialGraph.prefixState (caller (bits + 2)) edge .contradiction) combined index).2 =
        caller (bits + 2) := by
  obtain ⟨combined, receipt, child, frame, fits, post⟩ := SourceCurrentInheritedNumeric.prefix_descent formulas solver inventory
    edge .contradiction index (caller (bits + 2)) EndpointMemoGateTrace.empty (context _ formulas solver)
    (initial_frame bits formulas solver) profile (initial_fits _)
    (fun different => False.elim (different rfl)) (fun different => False.elim (different rfl))
  have same : combined = .contradiction := Option.some.inj (Except.ok.inj receipt.actual.symm)
  subst combined
  exact ⟨.contradiction, receipt, child, frame, fits, post, rfl, rfl⟩

/-- Actual descent allocates its new field and then reuses the exact full warm caller. -/
theorem constructed_allocating_warm (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    let first := SourceCurrentAllocatedPartialGraph.descend (caller (bits + 2)) field 0
    SourceCurrentAllocatedPartialDescent.Receipt formulas solver inventory (caller (bits + 2)) field 0 ∧
      SourceCurrentAllocatedPartialDescent.Receipt formulas solver inventory first.2 field 0 ∧
      Frame formulas solver inventory (SourceCurrentAllocatedPartialGraph.descend first.2 field 0).2.checked ∧
      Fits profile (SourceCurrentAllocatedPartialGraph.descend first.2 field 0).2.checked ∧
      SourceCurrentAllocatedPartialInvariant.Post formulas solver inventory (caller (bits + 2))
        (SourceCurrentAllocatedPartialGraph.descend first.2 field 0).2 EndpointMemoGateTrace.empty ∧
      first.2.checked.operations.constraints.next = operations.constraints.next + 1 ∧
      SourceCurrentAllocatedPartialGraph.descend first.2 field 0 = (first.1, first.2) := by
  dsimp only
  obtain ⟨firstReceipt, firstFrame, firstFits, firstPost⟩ := SourceCurrentInheritedNumeric.descent formulas solver inventory
    (caller (bits + 2)) EndpointMemoGateTrace.empty field 0 (context _ formulas solver) (initial_frame bits formulas solver)
    profile (initial_fits _) field_ready
  have ready := field_ready.grows firstReceipt.effects.grows.constraint_growth
  obtain ⟨lastReceipt, lastFrame, lastFits, lastPost⟩ := SourceCurrentInheritedNumeric.descent formulas solver inventory
    (SourceCurrentAllocatedPartialGraph.descend (caller (bits + 2)) field 0).2 EndpointMemoGateTrace.empty field 0
    firstPost.context firstFrame profile firstFits ready
  refine ⟨firstReceipt, lastReceipt, lastFrame, lastFits, firstPost.trans lastPost, ?_, ?_⟩
  · cbv
  · cbv

end MicroCFTA.InheritedNumericKernels
