import MicroCFTA.SourceSynthesisNativeTypeScan
import MicroCFTA.SourceSynthesisNativeTypeSeededWorker
import MicroCFTA.SourceCurrentAllocatedScanWorkerStability
import MicroCFTA.SourceCurrentConjunctionClassScanCompletion

/-!
# Type-ready graphs from actual current scan returns

The literal worker return supplies each reached gate, query and decision.
Their actual returned states derive the next Type-ready entry. The word
plan supplies only reached native bounds. No Scan graph, memo correctness,
semantic inventory, or future readiness is supplied.
These laws concern completed returns and do not prove scan termination.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeScanWorker
open InternedConstructorTemplates InternedProbeProvenance EqualityNormalize
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan (Scan advanceHeap)
open SourceCurrentAllocatedScanWorkerStability (bind_done_iff select_done_iff)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Ready" => SourceSynthesisNativeTypeClosedRequests.Ready
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "Ranges" => SourceCurrentConjunctionClassScanCompletion.Ranges
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
variable {width : Nat}

private theorem primary_return [DecidableEq (EdgeKey Symbol Guard)]
    {g : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after : Checked width} {memo saved : Memo} {answer : Bool}
    (actual : SourceCurrentAllocatedScanWorker.gate true g values paths before memo = .done answer after saved) :
    ∃ heap, EndpointStatefulGateTrace.ClassTrace source reaches values paths before.native.machine.heap answer heap ∧
      after = advanceHeap before heap ∧ saved = memo := by
  cases observed : SourceCurrentAllocatedGateWorker.primary g values paths before with
  | failed => simp only [SourceCurrentAllocatedScanWorker.gate, ite_true, observed] at actual; cases actual
  | done value current =>
      simp only [SourceCurrentAllocatedScanWorker.gate, ite_true, observed] at actual
      cases actual
      exact ⟨after.native.machine.heap, SourceCurrentAllocatedGateWorker.primary_graph observed,
        (SourceCurrentAllocatedGateWorker.primary_done observed).2, rfl⟩

private theorem secondary_return [DecidableEq (EdgeKey Symbol Guard)]
    {s : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after : Checked width} {memo saved : Memo} {answer : Bool}
    (actual : SourceCurrentAllocatedScanWorker.gate false s values paths before memo = .done answer after saved) :
    ∃ heap, SourceCurrentSecondaryTrace.ClassTrace source values paths before.native.machine.heap answer heap ∧
      after = advanceHeap before heap ∧ saved = memo := by
  cases observed : SourceCurrentAllocatedGateWorker.secondary s values paths before with
  | failed =>
      simp only [SourceCurrentAllocatedScanWorker.gate, Bool.false_eq_true, ite_false, observed] at actual
      cases actual
  | done value current =>
      simp only [SourceCurrentAllocatedScanWorker.gate, Bool.false_eq_true, ite_false, observed] at actual
      cases actual
      exact ⟨after.native.machine.heap, SourceCurrentAllocatedGateWorker.secondary_graph observed,
        (SourceCurrentAllocatedGateWorker.secondary_done observed).2, rfl⟩

private theorem query_return [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h n : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after : Checked width} {memo saved : Memo} {value : Value Symbol Guard}
    (actual : SourceCurrentAllocatedScanWorker.query p h n values paths before memo = .done value after saved) :
    SourceCurrentAllocatedSeededWorker.seeded p h n values (paths.map (List.map Int.ofNat)) before = .done value after ∧
      saved = memo := by
  cases observed : SourceCurrentAllocatedSeededWorker.seeded p h n values (paths.map (List.map Int.ofNat)) before with
  | failed => simp only [SourceCurrentAllocatedScanWorker.query, observed] at actual; cases actual
  | done result current =>
      simp only [SourceCurrentAllocatedScanWorker.query, observed] at actual
      cases actual
      exact ⟨rfl, rfl⟩

private theorem decision_return [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    {p h budget : Nat} {paths : Class} {value : Value Symbol Guard}
    {before after : Checked width} {memo saved : Memo} {answer : Bool}
    (actual : SourceCurrentAllocatedScanWorker.decision p h budget paths value before memo = .done answer after saved) :
    ∃ later : Physical, SourceCurrentConjunctionTupleExecution.Call budget memo value (physical before) answer later saved ∧
      after = advancePhysical before later := by
  cases observed : SourceCurrentAllocatedConjunctionWorker.call p h budget value before memo with
  | failed => simp only [SourceCurrentAllocatedScanWorker.decision, observed] at actual; cases actual
  | done result current fourth =>
      simp only [SourceCurrentAllocatedScanWorker.decision, observed] at actual
      cases actual
      obtain ⟨later, returned, same⟩ := SourceCurrentAllocatedConjunctionWorker.call_done observed
      exact ⟨later, SourceCurrentConjunctionTupleExecution.call_graph returned, same⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- A literal successful scan derives its own current graph from local Type facts. -/
theorem scan_graph (lib : Library) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (g s p h n budget : Nat)
    (values : List (Value Symbol Guard)) (classes : Constraints) (before : Checked width) (memo : Memo)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ paths ∈ classes, ∀ path ∈ paths, ForestPath (Origin lib) (path.map Int.ofNat) values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap)
    (ranges : Ranges budget source reaches values classes before memo)
    (outcome : Option Class) (selected : Constraints) (after : Checked width) (saved : Memo)
    (done : SourceCurrentAllocatedScanWorker.scan g s p h n budget values classes before memo =
      .done (outcome, selected) after saved) :
    Scan budget source reaches values classes before memo outcome selected after saved := by
  cases view : classes with
  | nil =>
      simp only [view, SourceCurrentAllocatedScanWorker.scan] at done
      cases done
      exact .nil
  | cons paths tail =>
      have tailRoutes : ∀ other ∈ tail, ∀ path ∈ other, ForestPath (Origin lib) (path.map Int.ofNat) values := by
        intro other member
        apply routes other
        rw [view]
        exact List.mem_cons_of_mem _ member
      have reachedRanges : Ranges budget source reaches values (paths :: tail) before memo := by
        simpa only [view] using ranges
      simp only [view, SourceCurrentAllocatedScanWorker.scan] at done
      obtain ⟨first, middle, current, primaryDone, remaining⟩ := (bind_done_iff _ _ _ _ _).mp done
      obtain ⟨heap, primary, rfl, rfl⟩ := primary_return primaryDone
      obtain ⟨firstReady, firstCosts, _, firstGuards, firstAvailable⟩ :=
        SourceSynthesisNativeTypeGate.primary lib source reaches primary ready costs available guards
      cases first with
      | false =>
          simp only [Bool.false_eq_true, ite_false] at remaining
          obtain ⟨rest, restDone, returned⟩ := (select_done_iff paths _ _ _ _).mp remaining
          obtain ⟨tailOutcome, tailSelected⟩ := rest
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj returned
          exact .selected primary (scan_graph lib formulas solver g s p h n budget values tail _ _
            firstReady firstCosts firstAvailable closed tailRoutes firstGuards (reachedRanges.1 heap primary)
            _ tailSelected after saved restDone)
      | true =>
          simp only [ite_true] at remaining
          obtain ⟨second, later, fourth, secondaryDone, laterDone⟩ := (bind_done_iff _ _ _ _ _).mp remaining
          obtain ⟨anchor, secondary, rfl, rfl⟩ := secondary_return secondaryDone
          obtain ⟨secondReady, secondCosts, _, secondGuards, secondAvailable⟩ :=
            SourceSynthesisNativeTypeGate.secondary lib source secondary firstReady firstCosts firstAvailable firstGuards
          cases second with
          | true =>
              simp only [ite_true] at laterDone
              exact .skipped primary secondary (scan_graph lib formulas solver g s p h n budget values tail _ _
                secondReady secondCosts secondAvailable closed tailRoutes secondGuards
                (reachedRanges.2.1 heap primary anchor secondary) outcome selected after saved laterDone)
          | false =>
              simp only [Bool.false_eq_true, ite_false] at laterDone
              have reached := reachedRanges.2.2 heap primary anchor secondary
              obtain ⟨query, checked, fourth, queryDone, calledDone⟩ := (bind_done_iff _ _ _ _ _).mp laterDone
              obtain ⟨seededDone, rfl⟩ := query_return queryDone
              have signedRoutes : ∀ path ∈ paths.map (List.map Int.ofNat), ForestPath (Origin lib) path values := by
                intro path member
                obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
                exact routes paths (by rw [view]; exact List.mem_cons_self) original included
              obtain ⟨seeded, queryReady, queryCosts, queryExtension, queryAvailable, _, _, queryGuards⟩ :=
                SourceSynthesisNativeTypeSeededWorker.seeded lib p h n values _ _ secondReady secondCosts
                  secondAvailable closed signedRoutes secondGuards reached.1 query checked seededDone
              obtain ⟨answer, lastChecked, finalMemo, decisionDone, restDone⟩ := (bind_done_iff _ _ _ _ _).mp calledDone
              obtain ⟨physicalAfter, called, rfl⟩ := decision_return decisionDone
              obtain ⟨lastReady, lastCosts, lastExtension, lastGuards⟩ :=
                SourceSynthesisNativeTypeScan.decision lib formulas solver called queryReady queryCosts queryAvailable queryGuards
              have lastAvailable : Values physicalAfter.heap values :=
                fun value member => lastExtension.available value (queryExtension.available value (secondAvailable value member))
              cases answer with
              | true =>
                  simp only [ite_true] at restDone
                  cases restDone
                  exact .stopped primary secondary seeded called
              | false =>
                  simp only [Bool.false_eq_true, ite_false] at restDone
                  exact .continued primary secondary seeded called (scan_graph lib formulas solver g s p h n budget
                    values tail _ finalMemo lastReady lastCosts lastAvailable closed tailRoutes lastGuards
                    (reached.2 query checked seeded physicalAfter finalMemo called) outcome selected after saved restDone)
termination_by classes.length
decreasing_by all_goals simp_all only [List.length_cons]; omega

/-- The same literal return derives its graph and joint warm Type invariants. -/
theorem scan (lib : Library) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (g s p h n budget : Nat)
    (values : List (Value Symbol Guard)) (classes : Constraints) (before : Checked width) (memo : Memo)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ paths ∈ classes, ∀ path ∈ paths, ForestPath (Origin lib) (path.map Int.ofNat) values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap)
    (ranges : Ranges budget source reaches values classes before memo)
    (outcome : Option Class) (selected : Constraints) (after : Checked width) (saved : Memo)
    (done : SourceCurrentAllocatedScanWorker.scan g s p h n budget values classes before memo =
      .done (outcome, selected) after saved) :
    Scan budget source reaches values classes before memo outcome selected after saved ∧
      Ready lib after ∧ CostHeap after.native.machine.heap ∧
      Extension before.native.machine after.native.machine ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ Values after.native.machine.heap values := by
  have graph := scan_graph lib formulas solver g s p h n budget values classes before memo ready costs
    available closed routes guards ranges outcome selected after saved done
  exact ⟨graph, SourceSynthesisNativeTypeScan.scan lib formulas solver graph ready costs available closed routes guards⟩

end MicroCFTA.SourceSynthesisNativeTypeScanWorker
