import MicroCFTA.SourceCurrentOuterInitialEdgeMemoFailure
import MicroCFTA.SourceCurrentOuterParentFailure
import MicroCFTA.SourceCurrentParentGuardAlphabet
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

namespace MicroCFTA.OuterEdgeIdleKernels
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
private def expression : Syntax Symbol Guard :=
  .node [.mk ("outer", .top) annotation [
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
private def emptyOriginal : Guard := ⟨some [], .top⟩
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
private def seed := (alphabet, profile)
private def request : SourceCurrentAllocatedPartialState.NodeRequest := ⟨emptyField, value⟩
private theorem inherited_ready (width : Nat) :
    SourceEqualityConstraintAllocation.Ready (before width).operations.constraints request.inherited := by
  have loaded : SourceEqualityConstraintFieldLookup.load emptyOriginal operations.constraints =
      .ok (some (⟨emptyField, .top⟩ : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)) := by cbv
  exact (SourceEqualityConstraintFieldLookup.load_ready emptyOriginal operations.constraints
    (initial width).1.good.operations.constraints SourceEqualityGuardReadback.empty_cached _ loaded).1
private theorem known (width : Nat) : SourceEqualityAnnotationHeap.Heap
    (fun guard => guard ∈ alphabet) (before width).native.machine.heap :=
  SourceCurrentConjunctionGuardUniverse.initial heap (initial width).1.good.native.machine.1
private def start (width : Nat) : SourceCurrentOuterCopiedWarmHit.Phase width := .node 2 request (caller width)
private def low (width : Nat) := SourceCurrentOuterActiveAncestry.run 0 0 0 0 0 0 0 0 0 0 (start width)
private def lowFault (width : Nat) : SourceCurrentAllocatedParentWorker.Fault width :=
  match low width with
  | .failed (.parent observation) _ => observation
  | _ => .missingField
private def lowAfter (width : Nat) := (low width).state
private theorem low_failed (width : Nat) : low width = .failed (.parent (lowFault width)) (lowAfter width) := by
  have tag : (match low width with | .failed (.parent _) _ => true | _ => false) = true := by cbv
  cases observed : low width with
  | done result after => rw [observed] at tag; cases tag
  | failed fault after =>
    cases fault <;> simp_all only [lowFault, lowAfter, SourceCurrentAllocatedPartialWorker.Outcome.state, Bool.false_eq_true]
private def widthBits := SourceCurrentParentInitialRoom.roomBits
  (SourceCurrentOuterInitialPrefix.forecast 0 (start 0) seed).2

private def sourceRows : List (EdgeValue Symbol Guard) :=
  match value with | .node _ rows _ _ => rows | _ => []
private def edgeOwner : SourceCurrentAllocatedPartialState.EdgeRequest :=
  ⟨emptyField, sourceRows[0]'(by cbv)⟩
private theorem low_owner (width : Nat) :
    (lowAfter width).edgeResults.cells 0 = some ⟨edgeOwner,.evaluating⟩ := by cbv
private def Claim (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
  built = .done value heap ∧ (∀ depth, ¬Cap depth recursive) ∧
  SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory (caller (widthBits+2)) EndpointMemoGateTrace.empty ∧
  low (widthBits+2) = .failed (.parent (lowFault (widthBits+2))) (lowAfter (widthBits+2)) ∧
  (lowAfter (widthBits+2)).edgeResults.cells 0 = some ⟨edgeOwner,.evaluating⟩ ∧
  (∃ fuel inherited original rest before,
    SourceCurrentOuterExecutionAncestry.Reached 0 0 0 0 0 0 0 0 0 0 (start (widthBits+2))
      (.rows (fuel+1) inherited (original::rest) before) ∧
    SourceCurrentOuterEdgeIdle.EdgeIdle before ∧
    SourceCurrentAllocatedPartialWorker.edgeCall fuel 0 0 0 0 0 0 0 0 0 0 ⟨inherited,original⟩ before =
      .failed (.parent (lowFault (widthBits+2))) (lowAfter (widthBits+2))) ∧
  ∀ g s r e p h m c n handle observation after,
    SourceCurrentOuterActiveAncestry.run g s r e p h m c n 0 (start (widthBits+2)) ≠
      .failed (.edgeMemo handle observation) after
private theorem run (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) : Claim formulas solver := by
  refine ⟨constructed,no_cap,context (widthBits+2) formulas solver,low_failed _,low_owner _,?_,?_⟩
  · obtain ⟨fuel,inherited,original,rest,before,actual,failed⟩ := SourceCurrentOuterParentFailure.failed
      (low_failed (widthBits+2))
    exact ⟨fuel,inherited,original,rest,before,actual,
      SourceCurrentOuterEdgeIdleReached.reached actual (SourceCurrentOuterEdgeIdle.initial _ _ _),failed⟩
  · intro g s r e p h m c n handle observation after
    exact SourceCurrentOuterInitialEdgeMemoFailure.no_edge_memo_failure formulas solver
      (phase := start (widthBits+2)) (budget := 0) seed
      (context (widthBits+2) formulas solver) (initial_frame widthBits formulas solver)
      (initial_fits (widthBits+2)) (known (widthBits+2))
      ⟨inherited_ready (widthBits+2),(initial (widthBits+2)).2.1⟩
      (SourceCurrentParentInitialRoom.room_computed _) (SourceCurrentOuterEdgeIdle.initial _ _ _)
      handle observation after

/-- Actual phase entries stay edge-idle although the same run's terminal Parent fault retains its owner. -/
theorem phase_idle_and_terminal_owner (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) : Claim formulas solver := run formulas solver

end MicroCFTA.OuterEdgeIdleKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000


#check @MicroCFTA.OuterEdgeIdleKernels.Claim
#print MicroCFTA.OuterEdgeIdleKernels.Claim
#print axioms MicroCFTA.OuterEdgeIdleKernels.Claim
