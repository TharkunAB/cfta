import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryScan
namespace FiniteOrdinaryScanKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance EqualityNormalize
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedFiniteOrdinaryScan
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Domain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "Scan" => SourceCurrentConjunctionClassScan.Scan
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- A supplied Scan retains its own inventory and all three distinct memo certificates. -/
theorem supplied_retains_all
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    {budget : Nat} {values : List (Value Symbol Guard)} {classes selected : Constraints}
    {before after : Checked width} {memo saved : Memo} {outcome : Option Class} (memos : Memos)
    (actual : Scan budget sourceGate sourceReaches values classes before memo outcome selected after saved)
    (ready : Ready before) (available : Values before.native.machine.heap values) (domain : Domain values)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (native : SourceCurrentAllocatedFiniteOrdinaryStored.Stored before.native)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    SourceCurrentAllocatedScanSourceReads.ScanReads actual memos memos ∧ Ready after ∧
      SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory after ∧
      SourceCurrentAllocatedFiniteOrdinaryStored.Stored after.native ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
      EndpointMemoGateTrace.Valid after.native.machine.heap memos ∧ outcome = none ∧ selected = classes := by
  obtain ⟨outcomeSame, selectedSame, afterSame, memoSame, reads⟩ := verified actual ready available domain memos
  subst after saved
  exact ⟨reads, ready, admitted, native, correct, valid, outcomeSame, selectedSame⟩

/-- Two constructed scans reuse the warm state and retain repeated classes and unequal path lengths. -/
theorem serial_constructed (budget : Nat) (values : List (Value Symbol Guard)) (before : Checked width)
    (memo : Memo) (memos : Memos) (ready : Ready before)
    (available : Values before.native.machine.heap values) (domain : Domain values) :
    let classes : Constraints := [[[0], [0, 0]], [[0], [0, 0]]]
    ∃ first : Scan budget sourceGate sourceReaches values classes before memo none classes before memo,
      SourceCurrentAllocatedScanSourceReads.ScanReads first memos memos ∧
      ∃ second : Scan budget sourceGate sourceReaches values (classes ++ classes) before memo none (classes ++ classes) before memo,
        SourceCurrentAllocatedScanSourceReads.ScanReads second memos memos := by
  dsimp only
  obtain ⟨first, firstReads⟩ := construct budget values _ before memo ready available domain memos
  have next := scan first ready available domain
  obtain ⟨second, secondReads⟩ := construct budget values _ before memo (next.2.2.1 ▸ ready)
    (next.2.2.1 ▸ available) domain memos
  exact ⟨first, firstReads, second, secondReads⟩

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- A zero-fuel reached node still fails; the positive-fuel fast branch does not erase this boundary. -/
theorem reached_zero (before : Checked width) (value : Value Symbol Guard) :
    SourceCurrentAllocatedGateWorker.primary 0 [value] [[0]] before =
      .failed (.primary (.done none before.native.machine.heap)) before := by
  simp only [SourceCurrentAllocatedGateWorker.primary, SourceCurrentMuEndpoint.classMeets,
    InternedFreshOrdinaryStatefulGate.anyKnown, SourceCurrentMuEndpoint.meets,
    InternedFreshOrdinaryStatefulGate.child, List.getElem?_cons_zero,
    SourceCurrentMuEndpoint.nodeMeets, InternedNestedConstruction.Outcome.bind,
    SourceCurrentAllocatedGateWorker.lift, advanceHeap_self]
end FiniteOrdinaryScanKernels
#print axioms FiniteOrdinaryScanKernels.supplied_retains_all
#check @FiniteOrdinaryScanKernels.supplied_retains_all
#print axioms FiniteOrdinaryScanKernels.serial_constructed
#check @FiniteOrdinaryScanKernels.serial_constructed
#print axioms FiniteOrdinaryScanKernels.reached_zero
#check @FiniteOrdinaryScanKernels.reached_zero
