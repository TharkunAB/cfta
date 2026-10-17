import MicroCFTA.SourceCurrentDescendantsNumeric
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

namespace MicroCFTA.DescendantsNumericKernels
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

private def annotation : Guard := ⟨none, .top⟩
private def emptyOriginal : Guard := ⟨some [], .top⟩
private def expression : Syntax Symbol Guard :=
  .node [.mk ("erase", .top) annotation [
    .node [.mk ("finite", .top) annotation [.node [.mk ("left", .top) annotation []], .node [.mk ("right", .top) annotation []]]],
    .binder false (.node [.mk ("pair", .top) annotation [.var 0, .var 0]])],
    .mk ("zero", .top) emptyOriginal []]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def finite : Value Symbol Guard := ((children value)[0]?).getD .empty
private def recursive : Value Symbol Guard := ((children value)[1]?).getD .empty
private def allocated := SourceEqualityConstraintAllocation.construct annotation.equalities Cache.emptyState
private def field : SourceEqualityConstraintAllocation.Value := match allocated.1 with
  | .ok value => value
  | .error _ => .contradiction
private def allocatedEmpty := SourceEqualityConstraintAllocation.construct emptyOriginal.equalities allocated.2
private def emptyField : SourceEqualityConstraintAllocation.Value := match allocatedEmpty.1 with
  | .ok own => own
  | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial allocatedEmpty.2
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def before (width : Nat) : Checked width := ⟨initial width machine, operations⟩

private theorem cached : SourceEqualityGuardReadback.Cached annotation.equalities := by
  intro classes impossible
  cases impossible
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
      have options : original = annotation ∨ original = emptyOriginal := by
        simpa [expression, SourceEqualityConstraintOrigins.guards,
          SourceEqualityConstraintOrigins.edgeGuards, SourceEqualityConstraintOrigins.childGuards] using member
      rcases options with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self) value heap constructed
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
  have count : (InternedEdgeResidency.nodeEdges value).length = 2 := by cbv
  have never : (2 : Nat) = 0 := count.symm.trans (congrArg List.length absent)
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

private def zeroRow : EdgeValue Symbol Guard := ((InternedEdgeResidency.nodeEdges value)[1]?).getD row
private theorem zero_resident : InternedEdgeResidency.EdgeResident heap zeroRow :=
  InternedEdgeResidency.resident_edges heap (initial 0).1.good.native.machine.1.linked value (initial 0).2.1.resident
    zeroRow (by cbv; exact .tail _ (.head _))

/-- A live inherited value combines with its actual contradictory own field and erases two slots. -/
theorem constructed_live_contradiction (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth recursive) ∧ emptyField ≠ .contradiction ∧ row.children.length = 2 ∧
      (SourceCurrentAllocatedInheritedPrefix.run row.entry.key.constraint emptyField operations).1 = .ok (some .contradiction) ∧
      ∃ result after, SourceCurrentDescendantsNumeric.Receipt formulas solver inventory profile 0 emptyField row
        (caller (bits + 2)) EndpointMemoGateTrace.empty result after := by
  have done : (SourceCurrentAllocatedInheritedPrefix.run row.entry.key.constraint emptyField operations).1 =
      .ok (some .contradiction) := by cbv
  obtain ⟨result, after, receipt⟩ := SourceCurrentDescendantsNumeric.terminal_complete formulas solver inventory 0 emptyField row
    (caller (bits + 2)) EndpointMemoGateTrace.empty (context _ formulas solver) (initial_frame bits formulas solver)
    profile (initial_fits _) row_resident empty_ready (Or.inl done)
  refine ⟨no_cap, ?_, ?_, done, result, after, receipt⟩
  · cbv
    intro impossible
    cases impossible
  · cbv
/-- A live zero-arity edge constructs its own prefix, empty walk, and full zero-fuel return. -/
theorem constructed_zero_live (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    zeroRow.children = [] ∧ emptyField ≠ .contradiction ∧
      (SourceCurrentAllocatedInheritedPrefix.run zeroRow.entry.key.constraint emptyField operations).1 = .ok (some emptyField) ∧
      ∃ result after, SourceCurrentDescendantsNumeric.Receipt formulas solver inventory profile 0 emptyField zeroRow
        (caller (bits + 2)) EndpointMemoGateTrace.empty result after := by
  have nilChildren : zeroRow.children = [] := by cbv
  obtain ⟨result, after, receipt⟩ := SourceCurrentDescendantsNumeric.terminal_complete formulas solver inventory 0 emptyField zeroRow
    (caller (bits + 2)) EndpointMemoGateTrace.empty (context _ formulas solver) (initial_frame bits formulas solver)
    profile (initial_fits _) zero_resident empty_ready (Or.inr nilChildren)
  refine ⟨nilChildren, ?_, ?_, result, after, receipt⟩
  · cbv
    intro impossible
    cases impossible
  · cbv
end MicroCFTA.DescendantsNumericKernels
