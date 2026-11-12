import MicroCFTA.SourcePruningEnumerationSharedScanReadsProjectable
import MicroCFTA.SourceCurrentSharedScanRequiredNumeric
import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceEqualityEmptyPropagation

/-!
# Source guard support through actual shared preparation reads

The actual preparation retains its stopped scan or completed required call.
Both branches preserve support at that same physical endpoint.
Original and returned values remain available in the returned heap.
This component does not construct a new preparation or parent execution.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparationReadsProjectable
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Record" => SourceEqualityClassOrder.Record
local notation "SupportedGuard" =>
  (fun guard : Guard => ∃ classes, SourceCompactGuards.sourceEqualities guard = some classes)
local notation "Heap" => SourceEqualityAnnotationHeap.Heap SupportedGuard
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- The same actual preparation reads retain both value lists and source guard support. -/
theorem preparation_reads_projectable
    {budget : Nat} {records kept : List Record} {values results : List Node}
    {before after : Checked width} {fourth saved : Memo} {outcome : Option EqualityNormalize.Class}
    {memos final : Memos}
    {actual : SourceCurrentSharedScanRequiredNumeric.Execution budget records values before fourth
      outcome kept results after saved}
    (reads : SourceCurrentSharedScanRequiredNumeric.Reads actual memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (current : Heap before.native.machine.heap) :
    Values after.native.machine.heap values ∧ Values after.native.machine.heap results ∧
      Heap after.native.machine.heap := by
  cases reads with
  | stopped scanned =>
      obtain ⟨_checked, originals, fields⟩ :=
        SourcePruningEnumerationSharedScanReadsProjectable.scan_reads_projectable
          scanned ready available proper current
      exact ⟨originals, (SourceEqualityEmptyPropagation.erased_scope _ _).1, fields⟩
  | @prepared _ _ _ middle _ _ heap
      _ _ _ _ _ requiredFuel readFuel _ required _ _ _ first _second =>
      obtain ⟨checked, originals, fields⟩ :=
        SourcePruningEnumerationSharedScanReadsProjectable.scan_reads_projectable
          first ready available proper current
      have returned := SourceCurrentRequiredHeapEffects.requireAll SupportedGuard requiredFuel readFuel
        (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths))
        values results middle.native.machine.heap heap required
        checked.semantic checked.costs fields originals
      exact ⟨fun value member => returned.1.available value (originals value member),
        returned.2.2.2.2, returned.2.2.2.1⟩

end MicroCFTA.SourcePruningEnumerationSharedPreparationReadsProjectable
