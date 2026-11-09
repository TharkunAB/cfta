import MicroCFTA.SourceEqualityRequiredPathShape
import MicroCFTA.SourceCurrentSharedScanRequiredNumeric
import MicroCFTA.SourceCurrentSharedParentProbeHeap

/-!
# Required path shapes at the actual shared preparation return

The observed shared Scan derives readiness at the literal Required entry.
Required retains its original forest and exact returned heap. A stopped
Scan returns literal empty slots. No later class-pass shape is claimed.
-/
namespace MicroCFTA.SourceCurrentSharedRequiredPathShape
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredPathShape (ChildrenShape PrefixShape)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Preparation" => SourceCurrentSharedScanRequiredNumeric.Execution
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Each observed shared preparation derives the shapes of its selected strict prefixes. -/
theorem execution_shape {budget records values}
    {before after : SourceEqualityNativeDemand.State width} {fourth outcome kept results saved}
    (actual : Preparation budget records values before fourth outcome kept results after saved)
    (good : SourceCurrentLowerProbeHeap.Good before)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values) :
    match SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) with
    | .node entries => ChildrenShape entries 0 results := by
  generalize compiled : SourceEqualityNeeded.build
    (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) = needed
  cases actual with
  | stopped observed =>
      cases needed with
      | node entries =>
          intro index value needed found selected
          have member := List.mem_of_getElem? found
          obtain ⟨original, _inside, same⟩ := List.mem_map.mp member
          cases same
          cases needed with
          | node inner => exact PrefixShape.empty inner
  | prepared observed required =>
      have mapped := congrArg SourceCurrentAllocatedSharedRecordScanWorker.mapPaths observed
      rw [SourceCurrentAllocatedSharedRecordScanWorker.scan_mapPaths] at mapped
      dsimp only [SourceCurrentAllocatedSharedRecordScanWorker.mapPaths] at mapped
      have scanned := SourceCurrentSharedParentProbeHeap.scan mapped good available
      have shape := SourceEqualityRequiredPathShape.requireAll_shape required scanned.good.heap
        (fun value member => scanned.keeps.available value (available value member)) closed
      cases needed with
      | node entries => simpa only [compiled] using shape

/-- Current caller facts attach shapes to the same shared numeric preparation receipt. -/
theorem receipt_shape
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory entryInventory profile budget records values before memos outcome kept results after saved final}
    (receipt : SourceCurrentSharedScanRequiredNumeric.Receipt (width := width)
      formulas solver inventory profile budget records values before memos outcome kept results after saved final)
    (initial : Context formulas solver entryInventory before memos)
    (available : Values before.checked.native.machine.heap values) (closed : ClosedValues values) :
    match SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) with
    | .node entries => ChildrenShape entries 0 results := by
  have good : SourceCurrentLowerProbeHeap.Good before.checked :=
    ⟨SourceCurrentNativeOperationHeap.Good.of_native
      (SourceCurrentNativeOperationInvariants.Good.of_checked initial.ready.good)
      initial.ready.semantic initial.ready.costs, initial.probes⟩
  exact execution_shape receipt.actual good available closed

end MicroCFTA.SourceCurrentSharedRequiredPathShape
