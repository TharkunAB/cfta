import MicroCFTA.SourceCurrentOuterInitialActual
import MicroCFTA.SourceCurrentOuterExecutionAncestry
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

namespace MicroCFTA.OuterPrefixKernels
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

private def sourceRows : List (EdgeValue Symbol Guard) :=
  match value with | .node _ rows _ _ => rows | _ => []
private def firstEdge : EdgeValue Symbol Guard := sourceRows[0]'(by cbv)
private def secondEdge : EdgeValue Symbol Guard := sourceRows[1]'(by cbv)
private def running (width : Nat) := (SourceCurrentAllocatedPartialState.beginNode request (caller width)).2.2
private def parentFirst (width : Nat) := SourceCurrentAllocatedPartialWorker.edgeCall
  2 0 0 0 0 0 0 0 0 0 0 ⟨emptyField,firstEdge⟩ (running width)
private def narrowedFirst (width : Nat) : EdgeValue Symbol Guard := match parentFirst width with
  | .done result _ => result | .failed .. => firstEdge
private def firstMiddle (width : Nat) := (parentFirst width).state
private def descendantsFirst (width : Nat) := SourceCurrentAllocatedPartialWorker.descendants
  2 0 0 0 0 0 0 0 0 0 0 emptyField (narrowedFirst width) (firstMiddle width)
private def firstResult (width : Nat) : EdgeValue Symbol Guard := match descendantsFirst width with
  | .done result _ => result | .failed .. => firstEdge
private def firstAfter (width : Nat) := (descendantsFirst width).state
private def parentSecond (width : Nat) := SourceCurrentAllocatedPartialWorker.edgeCall
  1 0 0 0 0 0 0 0 0 0 0 ⟨emptyField,secondEdge⟩ (firstAfter width)
private def narrowedSecond (width : Nat) : EdgeValue Symbol Guard := match parentSecond width with
  | .done result _ => result | .failed .. => secondEdge
private def secondMiddle (width : Nat) := (parentSecond width).state
private def prefixSecond (width : Nat) := SourceCurrentAllocatedInheritedPrefix.run
  (narrowedSecond width).entry.key.constraint emptyField (secondMiddle width).checked.operations
private def combined (width : Nat) : SourceEqualityConstraintAllocation.Value := match (prefixSecond width).1 with
  | .ok (some combined) => combined | _ => .contradiction
private def childBefore (width : Nat) := SourceCurrentAllocatedPartialGraph.prefixState
  (secondMiddle width) (narrowedSecond width) emptyField
private def selectedChild (width : Nat) : Value Symbol Guard :=
  (narrowedSecond width).children[0]'(by cbv)
private def remainingChild (width : Nat) : Value Symbol Guard :=
  (narrowedSecond width).children[1]'(by cbv)
private def selectedBefore (width : Nat) := SourceCurrentAllocatedPartialGraph.descend
  (childBefore width) (combined width) 0
private def selectedCall (width : Nat) := SourceCurrentAllocatedPartialWorker.nodeCall
  0 0 0 0 0 0 0 0 0 0 0 ⟨(selectedBefore width).1,selectedChild width⟩ (selectedBefore width).2
private def selectedResult (width : Nat) : Value Symbol Guard := match selectedCall width with
  | .done result _ => result | .failed .. => .empty
private def failedAfter (width : Nat) := (selectedCall width).state

open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
private def start (width : Nat) : Phase width := .node 4 request (caller width)
private def stop (width : Nat) : Phase width := .walk 0 (combined width) 1 [remainingChild width] (failedAfter width)

private theorem began (width : Nat) : SourceCurrentAllocatedPartialState.beginNode request (caller width) =
    (0,.evaluate request,running width) := by cbv
private theorem first_done (width : Nat) : parentFirst width = .done (narrowedFirst width) (firstMiddle width) := by
  have tag : (match parentFirst width with | .done .. => true | _ => false) = true := by cbv
  cases observed : parentFirst width <;> simp_all only [narrowedFirst,firstMiddle,SourceCurrentAllocatedPartialWorker.Outcome.state,Bool.false_eq_true]
private theorem descendants_done (width : Nat) : descendantsFirst width = .done (firstResult width) (firstAfter width) := by
  have tag : (match descendantsFirst width with | .done .. => true | _ => false) = true := by cbv
  cases observed : descendantsFirst width <;> simp_all only [firstResult,firstAfter,SourceCurrentAllocatedPartialWorker.Outcome.state,Bool.false_eq_true]
private theorem second_done (width : Nat) : parentSecond width = .done (narrowedSecond width) (secondMiddle width) := by
  have tag : (match parentSecond width with | .done .. => true | _ => false) = true := by cbv
  cases observed : parentSecond width <;> simp_all only [narrowedSecond,secondMiddle,SourceCurrentAllocatedPartialWorker.Outcome.state,Bool.false_eq_true]
private theorem prefix_done (width : Nat) : (prefixSecond width).1 = .ok (some (combined width)) := by cbv
private theorem selected_done (width : Nat) : selectedCall width = .done (selectedResult width) (failedAfter width) := by
  have tag : (match selectedCall width with | .done .. => true | _ => false) = true := by cbv
  cases observed : selectedCall width <;> simp_all only [selectedResult,failedAfter,SourceCurrentAllocatedPartialWorker.Outcome.state,Bool.false_eq_true]

private theorem shaped : ∃ entry depth free, value = .node entry [firstEdge,secondEdge] depth free := by
  have tag : (match value with | .node .. => true | _ => false) = true := by cbv
  have rows : sourceRows = [firstEdge,secondEdge] := by cbv
  cases observed : value with
  | empty | reference | union | mu => rw [observed] at tag; cases tag
  | node entry originals depth free =>
      have same : originals = [firstEdge,secondEdge] := by simpa only [sourceRows,observed] using rows
      exact ⟨entry,depth,free,by rw [same]⟩
private theorem second_children (width : Nat) : (narrowedSecond width).children = [selectedChild width,remainingChild width] := by cbv
private theorem reached (width : Nat) : Reached 0 0 0 0 0 0 0 0 0 0 (start width) (stop width) := by
  obtain ⟨entry,depth,free,shape⟩ := shaped
  have activated : Reached 0 0 0 0 0 0 0 0 0 0 (start width) (.body 4 request (running width)) :=
    .snoc (.refl _) (.node_evaluate (began width))
  have rows : Reached 0 0 0 0 0 0 0 0 0 0 (start width)
      (.rows 3 emptyField [firstEdge,secondEdge] (running width)) :=
    .snoc activated (.body_rows shape)
  have tail := Reached.snoc rows (Step.rows_tail (first_done width) (descendants_done width))
  have descend := Reached.snoc tail (Step.rows_edge (second_done width))
  have children := Reached.snoc descend (Step.descendants_children (prefix_done width))
  have live : combined width ≠ .contradiction := by cbv; intro impossible; cases impossible
  have walk := Reached.snoc children (Step.children_walk live)
  rw [second_children width] at walk
  exact Reached.snoc walk (Step.walk_tail (selected_done width))
private theorem stopped (width : Nat) : SourceCurrentOuterActiveAncestry.run 0 0 0 0 0 0 0 0 0 0 (stop width) =
    .failed (.exhausted .walk) (failedAfter width) := by
  simp only [stop,SourceCurrentOuterActiveAncestry.run,SourceCurrentAllocatedPartialWorker.walk,
    SourceCurrentAllocatedPartialWorker.Outcome.bind]
private theorem failed (width : Nat) : SourceCurrentAllocatedPartialWorker.nodeCall
    4 0 0 0 0 0 0 0 0 0 0 request (caller width) = .failed (.exhausted .walk) (failedAfter width) := by
  have failure := (reached width).failed (stopped width)
  change (SourceCurrentAllocatedPartialWorker.nodeCall 4 0 0 0 0 0 0 0 0 0 0 request (caller width)).bind
    (fun _ after => .done () after) = .failed (.exhausted .walk) (failedAfter width) at failure
  cases observed : SourceCurrentAllocatedPartialWorker.nodeCall 4 0 0 0 0 0 0 0 0 0 0 request (caller width) with
  | done result after => rw [observed] at failure; cases failure
  | failed fault after =>
      rw [observed] at failure
      exact observed.trans (by simpa only [SourceCurrentAllocatedPartialWorker.Outcome.bind] using failure)

end MicroCFTA.OuterPrefixKernels
