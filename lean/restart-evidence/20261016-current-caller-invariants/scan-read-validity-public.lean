import MicroCFTA.SourceCurrentAllocatedScanReadValidity

#check MicroCFTA.SourceCurrentAllocatedScanReadValidity.scan
#print axioms MicroCFTA.SourceCurrentAllocatedScanReadValidity.scan
#check MicroCFTA.SourceCurrentAllocatedScanReadValidity.construct
#print axioms MicroCFTA.SourceCurrentAllocatedScanReadValidity.construct

namespace MicroCFTA.SourceCurrentAllocatedScanReadValidityProbes
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionClassScan
open SourceCurrentAllocatedScanSourceReads (ScanReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "u" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches u
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Two actual scans retain their own shared globals and all earlier fourth answers. -/
theorem two_actual_scans
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {values : List (Value Symbol Guard)} {classes firstSelected more secondSelected : Constraints}
    {firstOutcome secondOutcome : Option Class} {before middle after : Checked width}
    {fourth nextFourth finalFourth : Memo} {memos nextMemos finalMemos : Memos}
    {first : Scan budget u reaches values classes before fourth firstOutcome firstSelected middle nextFourth}
    {second : Scan budget u reaches values more middle nextFourth secondOutcome secondSelected after finalFourth}
    (firstReads : ScanReads first memos nextMemos) (secondReads : ScanReads second nextMemos finalMemos)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (moreProper : ∀ paths ∈ more, ∀ path ∈ paths, path ≠ [])
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (firstRanges : SourceCurrentConjunctionClassScanCompletion.Ranges budget u reaches values classes before fourth)
    (secondRanges : SourceCurrentConjunctionClassScanCompletion.Ranges budget u reaches values more middle nextFourth)
    (valid : Valid before.native.machine.heap memos) :
    Valid after.native.machine.heap finalMemos ∧ Ready after ∧
      SourceCurrentConjunctionRowsAllocation.Effects
        (SourceCurrentAllocatedNativeEffects.physical before) (SourceCurrentAllocatedNativeEffects.physical after) ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap finalFourth ∧
      SourceCurrentEmptinessMemo.Extends fourth finalFourth := by
  have one := SourceCurrentAllocatedScanReadValidity.scan firstReads ready available proper formulas solver correct firstRanges valid
  have two := SourceCurrentAllocatedScanReadValidity.scan secondReads one.2.1 one.2.2.2.1 moreProper
    formulas solver one.2.2.2.2.1 secondRanges one.1
  exact ⟨two.1, two.2.1, one.2.2.1.trans two.2.2.1, two.2.2.2.2.1,
    fun key entry found => two.2.2.2.2.2 key entry (one.2.2.2.2.2 key entry found)⟩
end MicroCFTA.SourceCurrentAllocatedScanReadValidityProbes

#check MicroCFTA.SourceCurrentAllocatedScanReadValidityProbes.two_actual_scans
#print axioms MicroCFTA.SourceCurrentAllocatedScanReadValidityProbes.two_actual_scans
