import MicroCFTA.SourceSynthesisNativeTypeScanWorker
import MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual

/-!
# Type facts for literal scans of original record occurrences

Literal success derives the same Scan graph and each retained record.
Stable replay identifies occurrences even when their path lists agree.
The physical result needs no memo-answer correctness or language inventory.
Actual success and reached word ranges remain local premises.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeRecordScanWorker
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceEqualityClassOrder (Record)
open SourceCurrentConjunctionClassScan (Scan)
open SourceCurrentConjunctionSelectedRecords (Retained)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "Ready" => SourceSynthesisNativeTypeClosedRequests.Ready
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "Ranges" => SourceCurrentConjunctionClassScanCompletion.Ranges
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- A literal Type scan retains the same original record occurrences. -/
theorem scan_graph (lib : Library) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s p h n budget : Nat} {values : List (Value Symbol Guard)}
    {records kept : List Record} {outcome : Option EqualityNormalize.Class}
    {before after : Checked width} {memo saved : Memo}
    (done : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before memo =
      .done (outcome, kept) after saved)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ record ∈ records, ∀ path ∈ record.paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap)
    (ranges : Ranges budget source reaches values (records.map Record.paths) before memo) :
    ∃ actual : Scan budget source reaches values (records.map Record.paths) before memo
        outcome (kept.map Record.paths) after saved,
      Retained actual records kept := by
  have projected := congrArg SourceCurrentAllocatedRecordScanWorker.mapPaths done
  rw [SourceCurrentAllocatedRecordScanWorker.scan_mapPaths] at projected
  have paths : ∀ paths ∈ records.map Record.paths, ∀ path ∈ paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values := by
    intro paths included
    obtain ⟨record, member, rfl⟩ := List.mem_map.mp included
    exact routes record member
  have actual := SourceSynthesisNativeTypeScanWorker.scan_graph lib formulas solver
    g s p h n budget values (records.map Record.paths) before memo
    ready costs available closed paths guards ranges outcome (kept.map Record.paths) after saved projected
  obtain ⟨chosen, retained⟩ := SourceCurrentConjunctionSelectedRecords.retained_records records actual
  obtain ⟨G, S, P, H, N, stable⟩ := SourceCurrentAllocatedRecordScanWorkerActual.scan_complete retained
  obtain ⟨same, _, _⟩ := SourceCurrentAllocatedRecordScanWorkerStability.scan_done_unique
    (stable G S P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)) done
  have aligned : chosen = kept := congrArg Prod.snd same
  subst chosen
  exact ⟨actual, retained⟩

/-- Exact retained records and the actual returned Type state follow from literal success. -/
theorem scan (lib : Library) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s p h n budget : Nat} {values : List (Value Symbol Guard)}
    {records kept : List Record} {outcome : Option EqualityNormalize.Class}
    {before after : Checked width} {memo saved : Memo}
    (done : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before memo =
      .done (outcome, kept) after saved)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ record ∈ records, ∀ path ∈ record.paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap)
    (ranges : Ranges budget source reaches values (records.map Record.paths) before memo) :
    ∃ actual : Scan budget source reaches values (records.map Record.paths) before memo
        outcome (kept.map Record.paths) after saved,
      Retained actual records kept ∧ Ready lib after ∧ CostHeap after.native.machine.heap ∧
      Extension before.native.machine after.native.machine ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ Values after.native.machine.heap values := by
  obtain ⟨actual, retained⟩ := scan_graph lib formulas solver done ready costs available closed routes guards ranges
  have paths : ∀ paths ∈ records.map Record.paths, ∀ path ∈ paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values := by
    intro paths included
    obtain ⟨record, member, rfl⟩ := List.mem_map.mp included
    exact routes record member
  exact ⟨actual, retained,
    SourceSynthesisNativeTypeScan.scan lib formulas solver actual ready costs available closed paths guards⟩
end MicroCFTA.SourceSynthesisNativeTypeRecordScanWorker
