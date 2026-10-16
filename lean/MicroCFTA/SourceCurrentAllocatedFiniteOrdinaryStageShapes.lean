import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPassShapes
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequiredProfile
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentProfiles

/-!
# Numeric profiles through actual finite ordinary class stages

The primary Scan retains all original records and the same state.
Required paths retain the input row and arity bounds.
The class pass uses that actual Required return and memo bundle.
No constructor headroom or future result profile is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageShapes
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open MergedOrdinaryHeight (childrenHeight)

/-- The supplied stage reads derive numeric profiles at their exact class-pass return. -/
theorem profile_from_reads
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {records : List SourceEqualityClassOrder.Record}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {outcome : Option Class} {memos final : Memos}
    {actual : SourceCurrentConjunctionScanClassPass.Reduction budget records values before fourth memo outcome results after savedFourth saved}
    (reads : SourceCurrentConjunctionScanClassPassActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo) (output : OutputStored before.native)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound) :
    NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      ChildrenShape (SourceCurrentAllocatedFiniteOrdinaryPassResources.outputRows records rows count depth bound)
        (SourceCurrentAllocatedFiniteOrdinaryPassResources.outputArity records arity) results ∧
      All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results ∧
      results.length = values.length ∧ childrenHeight results ≤ bound := by
  have domain := ChildrenShape.domain values profile
  have ranges := SourceCurrentAllocatedFiniteOrdinaryScanRanges.scan_ranges budget sourceGate sourceReaches
    values (records.map SourceEqualityClassOrder.Record.paths) before fourth
    ready.good.native.machine.1.coherent available domain
  have pathsProper : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, ∀ path ∈ paths, path ≠ [] := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact proper record present
  have pathsActive : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, Nontrivial paths := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact (fields record present).2.2
  cases reads with
  | stopped scanRead =>
      rename_i paths selected scan
      have impossible := (SourceCurrentAllocatedFiniteOrdinaryScan.scan scan ready available domain).1
      cases impossible
  | completed first second last =>
      rename_i kept requiredValues middle selected heap fuel readFuel scanMemos requiredMemos required scan retained pass
      have unchanged := SourceCurrentAllocatedFiniteOrdinaryScan.scan scan ready available domain
      have sameLength : kept.length = records.length := by
        have lengths := congrArg List.length (retained.fields.2.trans unchanged.2.1)
        simpa only [List.length_map] using lengths
      have sameKept := retained.fields.1.eq_of_length sameLength
      subst kept
      have sameMiddle := unchanged.2.2.1
      cases sameMiddle
      obtain ⟨requiredInventory, requiredReceipt⟩ := SourceCurrentConjunctionRequiredActual.verified
        formulas solver inventory scan ready admitted available pathsProper pathsActive correct ranges required
      have scanValid := (SourceCurrentAllocatedScanReadValidity.scan first ready available pathsProper
        formulas solver correct ranges valid).1
      have requiredValid := (SourceCurrentAllocatedRequiredReadValidity.required second ready.semantic
        ready.costs available scanValid).1
      have narrowed := SourceCurrentAllocatedFiniteOrdinaryRequired.requireAll_done fuel readFuel
        (SourceEqualitySelectedRequired.paths selected) values requiredValues before.native.machine.heap heap
        required ready.semantic available domain
      have nativeAfter : NativeStored (advanceHeap before heap).native :=
        SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored before.native _ native
      have outputAfter : OutputStored (advanceHeap before heap).native :=
        SourceCurrentAllocatedFiniteOrdinaryOutputStored.advance_stored before.native _ output
      have requiredProfile := SourceCurrentAllocatedFiniteOrdinaryRequiredProfile.requireAll_done fuel readFuel
        (SourceEqualitySelectedRequired.paths selected) values requiredValues before.native.machine.heap heap
        required ready.semantic available profile
      have requiredHeight : childrenHeight requiredValues ≤ bound :=
        Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_height narrowed.2.2.2.2) heightBound
      have retainedFields := retained.fields
      have checked := SourceCurrentAllocatedFiniteOrdinaryClassPassShapes.pass formulas solver requiredInventory last
        (fun record member => (fields record (retainedFields.1.subset member)).1)
        (fun record member => (fields record (retainedFields.1.subset member)).2.2)
        requiredReceipt.ready requiredReceipt.admitted requiredReceipt.resident
        (physicalStored.grows requiredReceipt.effects.keeps) profiles nativeAfter outputAfter covered requiredValid
        rows arity count depth bound requiredProfile.2.2.2.1 (by rw [requiredProfile.2.2.2.2]; exact lengthBound)
        pathsBound requiredHeight
      exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1,
        SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_trans narrowed.2.2.2.2 checked.2.2.2.2.1,
        checked.2.2.2.2.2.1.trans requiredProfile.2.2.2.2, checked.2.2.2.2.2.2⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageShapes
