import MicroCFTA.SourceCurrentOuterInitialActual
import MicroCFTA.SourceCurrentParentInitialRoom
import MicroCFTA.SourceCurrentActualParentSemanticReads
import MicroCFTA.SourceCurrentParentNumeric
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceCurrentLocalNumeric
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
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 1000000

noncomputable section

namespace MicroCFTA.OuterInitialKernels
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

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small

private def annotation : Guard := ⟨some [[[0], [1]]], .top⟩
private def emptyOriginal : Guard := ⟨some [], .top⟩
private def expression : Syntax Symbol Guard :=
  .node [
    .mk ("outer", .top) emptyOriginal [
      .binder false (.node [.mk ("pair", .top) annotation [.var 0,.var 0]]),
      .binder false (.node [.mk ("pair", .top) annotation [.var 0,.var 0]])],
    .mk ("second", .top) emptyOriginal [
      .binder false (.node [.mk ("pair", .top) annotation [.var 0,.var 0]]),
      .binder false (.node [.mk ("pair", .top) annotation [.var 0,.var 0]])]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def finite : Value Symbol Guard := ((children value)[0]?).getD .empty
private def recursive : Value Symbol Guard := ((children value)[0]?).getD .empty
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
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
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
      have cases : original = emptyOriginal ∨ original = annotation := by
        have repeated : original = emptyOriginal ∨ original = annotation ∨ original = emptyOriginal ∨ original = annotation := by
          simpa [expression, SourceEqualityConstraintOrigins.guards,
            SourceEqualityConstraintOrigins.edgeGuards, SourceEqualityConstraintOrigins.childGuards] using member
        rcases repeated with same | same | same | same
        · exact Or.inl same
        · exact Or.inr same
        · exact Or.inl same
        · exact Or.inr same
      rcases cases with rfl | rfl
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_self) value heap constructed
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

private def values : List (Value Symbol Guard) := [finite, recursive]
private def caller (width : Nat) : SourceCurrentAllocatedPartialState.State width :=
  SourceCurrentAllocatedPartialState.initial (before width)
    SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private theorem available_values (width : Nat) : InternedNestedProvenance.Values heap values := by
  intro child member
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact (initial width).2.1.children finite (by cbv; exact .head _)
  · exact (initial width).2.1.children recursive (by cbv; exact .head _)
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
private def alphabet := SourceCurrentConjunctionGuardUniverse.guards heap
private def request : SourceCurrentAllocatedPartialState.NodeRequest := ⟨emptyField,value⟩
private def called (width : Nat) := SourceCurrentAllocatedPartialWorker.nodeCall
  5 0 0 0 0 0 0 0 0 0 0 request (caller width)
private def result (width : Nat) : Value Symbol Guard := match called width with
  | .done output _ => output
  | .failed .. => .empty
private def after (width : Nat) := (called width).state
private theorem called_done (width : Nat) : called width = .done (result width) (after width) := by
  have tag : (match called width with | .done .. => true | _ => false) = true := by cbv
  cases observed : called width <;> simp_all only [result,after,SourceCurrentAllocatedPartialWorker.Outcome.state,Bool.false_eq_true]
private def emptyLoaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula := ⟨emptyField,.top⟩
private theorem load_empty : SourceEqualityConstraintFieldLookup.load emptyOriginal operations.constraints = .ok (some emptyLoaded) := by cbv
private theorem inherited_ready (width : Nat) :
    SourceEqualityConstraintAllocation.Ready (before width).operations.constraints request.inherited :=
  (SourceEqualityConstraintFieldLookup.load_ready emptyOriginal operations.constraints
    (initial width).1.good.operations.constraints SourceEqualityGuardReadback.empty_cached emptyLoaded load_empty).1
private def seed := (alphabet,profile)
private def widthBits := SourceCurrentParentInitialRoom.roomBits
  (SourceCurrentOuterInitialSchedule.node 5 0 seed).2
private theorem known (width : Nat) : SourceEqualityAnnotationHeap.Heap
    (fun guard => guard ∈ alphabet) (before width).native.machine.heap :=
  SourceCurrentConjunctionGuardUniverse.initial heap (initial width).1.good.native.machine.1
private def sourceRows : List (EdgeValue Symbol Guard) :=
  match value with | .node _ rows _ _ => rows | _ => []
private theorem two_rows : sourceRows.length = 2 := by cbv

private def Claim (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
    built = .done value heap ∧ sourceRows.length = 2 ∧ (∀ depth, ¬Cap depth recursive) ∧
    called (widthBits+2) = .done (result (widthBits+2)) (after (widthBits+2)) ∧
    ∃ next final, ∃ actual : SourceCurrentAllocatedPartialGraph.NodeCall 0 request (caller (widthBits+2))
        (result (widthBits+2)) (after (widthBits+2)),
      SourceCurrentAllocatedPartialSourceReads.NodeCallReads formulas solver actual EndpointMemoGateTrace.empty final ∧
      SourceCurrentAllocatedPartialInvariant.Post formulas solver next (caller (widthBits+2)) (after (widthBits+2)) final ∧
      Frame formulas solver next (after (widthBits+2)).checked ∧
      Fits (SourceCurrentOuterInitialSchedule.node 5 0 seed).2 (after (widthBits+2)).checked ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (SourceCurrentOuterInitialSchedule.node 5 0 seed).1)
        (after (widthBits+2)).checked.native.machine.heap ∧
      SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request (result (widthBits+2)) ∧
      ∀ ambient term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient (result (widthBits+2)) term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term

private theorem actual_run (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) : Claim formulas solver := by
  have room := SourceCurrentParentInitialRoom.room_computed (SourceCurrentOuterInitialSchedule.node 5 0 seed).2
  obtain ⟨next,final,actual,reads,post,frame,numeric,carrier,_available,law⟩ :=
    SourceCurrentOuterInitialActual.node_call formulas solver 5 seed
      (context (widthBits+2) formulas solver) (initial_frame widthBits formulas solver)
      (initial_fits (widthBits+2)) (known (widthBits+2)) (inherited_ready (widthBits+2))
      (initial (widthBits+2)).2.1 room (called_done (widthBits+2))
  refine ⟨constructed,two_rows,no_cap,called_done (widthBits+2),next,final,actual,reads,post,frame,numeric,carrier,law,?_⟩
  intro ambient term
  apply (law ambient term).2
  have neutral : request.inherited.payload = some [] := by cbv
  rw [neutral]
  simp [SourceEqualityPrecheck.Sat, EqualityNormalize.Satisfies]

/-- A literal two-row recursive traversal derives its semantic law and all returned resources from initial facts. -/
theorem recursive_sibling_run (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) : Claim formulas solver :=
  actual_run formulas solver

end MicroCFTA.OuterInitialKernels
