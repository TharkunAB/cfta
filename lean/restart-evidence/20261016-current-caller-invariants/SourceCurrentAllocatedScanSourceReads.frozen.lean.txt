import MicroCFTA.SourceCurrentAllocatedPrimaryErase
import MicroCFTA.SourceCurrentConjunctionClassScanGlobalMemos

/-!
# Current Scan reads with exact primary source operands

Each primary read uses the exact physical node of its gate trace. Query
reads retain their existing actual secondary, seeded, and conjunction
receipts. Erasure preserves the complete Scan and both memo endpoints.
-/
namespace MicroCFTA.SourceCurrentAllocatedScanSourceReads
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan
open SourceCurrentConjunctionQueryGlobalMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "unconstrained" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches unconstrained
variable {width : Nat}

/-- Only reached calls carry their exact returned three-table bundle to the next branch. -/
inductive ScanReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)] :
    {budget : Nat} → {values : List (Value Symbol Guard)} → {classes selected : Constraints} →
    {outcome : Option Class} → {before after : Checked width} → {memo saved : Memo} →
    Scan budget unconstrained reaches values classes before memo outcome selected after saved → Memos → Memos → Prop where
  | nil : ScanReads .nil memos memos
  | selected (first : SourceCurrentAllocatedPrimaryReads.ClassReads primary memos middle)
      (tail : ScanReads rest middle final) : ScanReads (.selected primary rest) memos final
  | skipped (first : SourceCurrentAllocatedPrimaryReads.ClassReads primary memos middle)
      (second : SourceCurrentSecondaryMemos.ClassReads secondary middle later)
      (tail : ScanReads rest later final) : ScanReads (.skipped primary secondary rest) memos final
  | continued {budget : Nat} {values : List (Value Symbol Guard)} {paths : Class} {classes selected : Constraints}
      {before middle after : Checked width} {heap anchor : State Symbol Guard} {later : Physical}
      {query : Value Symbol Guard} {memo savedMemo saved : Memo} {outcome : Option Class}
      {primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.native.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor}
      {seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query middle}
      {call : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) false later savedMemo}
      {rest : Scan budget unconstrained reaches values classes (advancePhysical middle later)
        savedMemo outcome selected after saved}
      {memos first second final : Memos}
      (primaryRead : SourceCurrentAllocatedPrimaryReads.ClassReads primary memos first)
      (queryRead : QueryReads (before := advanceHeap before heap) secondary seeded call first second)
      (tailRead : ScanReads rest second final) :
      ScanReads (.continued primary secondary seeded call rest) memos final
  | stopped {budget : Nat} {values : List (Value Symbol Guard)} {paths : Class} {classes : Constraints}
      {before middle : Checked width} {heap anchor : State Symbol Guard} {later : Physical}
      {query : Value Symbol Guard} {memo saved : Memo}
      {primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.native.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor}
      {seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query middle}
      {call : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) true later saved}
      {memos first final : Memos}
      (primaryRead : SourceCurrentAllocatedPrimaryReads.ClassReads primary memos first)
      (queryRead : QueryReads (before := advanceHeap before heap) secondary seeded call first final) :
      ScanReads (.stopped (classes := classes) primary secondary seeded call) memos final

/-- Erasure retains the supplied actual Scan, all calls, and both complete memo bundles. -/
theorem ScanReads.erase [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {before after : Checked width} {memo saved : Memo} {actual : Scan budget unconstrained reaches values classes
      before memo outcome selected after saved} {memos final : Memos}
    (reads : ScanReads actual memos final) :
    SourceCurrentConjunctionClassScanGlobalMemos.ScanReads actual memos final := by
  induction reads with
  | nil => exact .nil
  | selected first tail ih => exact .selected (SourceCurrentAllocatedPrimaryReads.class_erase first) ih
  | skipped first second tail ih => exact .skipped (SourceCurrentAllocatedPrimaryReads.class_erase first) second ih
  | continued first query tail ih => exact .continued (SourceCurrentAllocatedPrimaryReads.class_erase first) query ih
  | stopped first query => exact .stopped (SourceCurrentAllocatedPrimaryReads.class_erase first) query

end MicroCFTA.SourceCurrentAllocatedScanSourceReads
