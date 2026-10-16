import MicroCFTA.SourceCurrentAllocatedScanWorkerCompletion

namespace MicroCFTA.ScanWorkerCompletionKernels
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan (Scan advanceHeap)
open SourceCurrentAllocatedScanWorker
open SourceCurrentAllocatedScanWorkerCompletion (StableRun scan_complete scan_uniform)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)] {width : Nat}

theorem actual_scan_retains_selected_occurrences
    {budget : Nat} {values : List (Value Symbol Guard)} {classes selected : Constraints}
    {before after : Checked width} {memo saved : Memo} {stopped : Option Class}
    (actual : Scan budget source reaches values classes before memo stopped selected after saved) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      scan fuel fuel fuel fuel fuel budget values classes before memo = .done (stopped, selected) after saved ∧
      selected.Sublist classes := by
  obtain ⟨bound, done⟩ := scan_uniform actual
  exact ⟨bound, fun fuel enough => ⟨done fuel enough, SourceCurrentConjunctionClassScan.selected_sublist actual⟩⟩

theorem stopped_needs_no_suffix
    {budget : Nat} {values : List (Value Symbol Guard)} {paths : Class} (suffix : Constraints)
    {heap anchor : State Symbol Guard} {before middle : Checked width}
    {queryValue : Value Symbol Guard} {memo saved : Memo}
    {later : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula}
    (primary : EndpointStatefulGateTrace.ClassTrace source reaches values paths before.native.machine.heap true heap)
    (secondary : SourceCurrentSecondaryTrace.ClassTrace source values paths heap false anchor)
    (query : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
      (advanceHeap (advanceHeap before heap) anchor) queryValue middle)
    (decision : SourceCurrentConjunctionMemo.Call budget memo queryValue (physical middle) true later saved) :
    StableRun (fun g s p h n => scan g s p h n budget values (paths :: suffix) before memo)
      (some paths, []) (advancePhysical middle later) saved :=
  scan_complete (.stopped primary secondary query decision)

theorem duplicate_selected_classes_keep_order
    {budget : Nat} {values : List (Value Symbol Guard)} {paths : Class} {before : Checked width}
    {firstHeap secondHeap : State Symbol Guard} (memo : Memo)
    (first : EndpointStatefulGateTrace.ClassTrace source reaches values paths before.native.machine.heap false firstHeap)
    (second : EndpointStatefulGateTrace.ClassTrace source reaches values paths
      (advanceHeap before firstHeap).native.machine.heap false secondHeap) :
    StableRun (fun g s p h n => scan g s p h n budget values [paths, paths] before memo)
      (none, [paths, paths]) (advanceHeap (advanceHeap before firstHeap) secondHeap) memo :=
  scan_complete (.selected first (.selected second .nil))

theorem warm_decision_hit_uses_no_lower_work
    (budget : Nat) (paths : Class) (queryValue original : Value Symbol Guard)
    (before : Checked width) (memo : Memo) (answer : Bool)
    (found : memo queryValue.referenceOf = some (original, answer)) :
    decision 0 0 budget paths queryValue before memo = .done answer before memo := by
  have done := SourceCurrentAllocatedConjunctionWorker.call_hit 0 0 budget queryValue original before memo answer found
  simp only [decision, done]

theorem empty_scan_keeps_full_state_and_fourth
    (g s p h n budget : Nat) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo) :
    scan g s p h n budget values [] before memo = .done (none, []) before memo := rfl

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
theorem selected_failure_keeps_prefix_and_observation (first second : Class) (fault : Fault width)
    (before : Checked width) (memo : Memo) :
    ((Outcome.failed fault before memo : Outcome Result width).select second).select first =
      .failed (.selected first (.selected second fault)) before memo := rfl

end MicroCFTA.ScanWorkerCompletionKernels

#print axioms MicroCFTA.ScanWorkerCompletionKernels.actual_scan_retains_selected_occurrences
#check @MicroCFTA.ScanWorkerCompletionKernels.actual_scan_retains_selected_occurrences
#print axioms MicroCFTA.ScanWorkerCompletionKernels.stopped_needs_no_suffix
#check @MicroCFTA.ScanWorkerCompletionKernels.stopped_needs_no_suffix
#print axioms MicroCFTA.ScanWorkerCompletionKernels.duplicate_selected_classes_keep_order
#check @MicroCFTA.ScanWorkerCompletionKernels.duplicate_selected_classes_keep_order
#print axioms MicroCFTA.ScanWorkerCompletionKernels.warm_decision_hit_uses_no_lower_work
#check @MicroCFTA.ScanWorkerCompletionKernels.warm_decision_hit_uses_no_lower_work
#print axioms MicroCFTA.ScanWorkerCompletionKernels.empty_scan_keeps_full_state_and_fourth
#check @MicroCFTA.ScanWorkerCompletionKernels.empty_scan_keeps_full_state_and_fourth
#print axioms MicroCFTA.ScanWorkerCompletionKernels.selected_failure_keeps_prefix_and_observation
#check @MicroCFTA.ScanWorkerCompletionKernels.selected_failure_keeps_prefix_and_observation
