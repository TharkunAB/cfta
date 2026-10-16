import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStage
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryScanRanges

/-!
# Numeric plans for the actual local Scan continuation

Only an earlier actual successful Scan and required-path return select a
class-pass capacity plan. Initial finite ordinary inputs derive the Scan
checks. The exact required return derives its domain and current facts.
No current class pass or future result invariant occurs in the plan.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageCapacity
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Scan Ready advanceHeap)
open SourceCurrentConjunctionSelectedRecords (Retained)
open SourceCurrentConjunctionScanClassPass (Reduction Receipt)
open SourceCurrentConjunctionScanClassPassActual (Reads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "PassCapacity" => SourceCurrentAllocatedFiniteOrdinaryPassCapacity.PassCapacity
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Only earlier Scan and required execution select the next numeric class-pass plan. -/
structure StageCapacity (bits budget : Nat) (records : List SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo) : Prop where
  pass : ∀ {selected middle savedFourth}
    (actual : Scan budget sourceGate sourceReaches values (records.map SourceEqualityClassOrder.Record.paths)
      before fourth none selected middle savedFourth),
    ∀ kept, Retained actual records kept → ∀ fuel readFuel requiredValues heap,
      SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
        values middle.native.machine.heap = .done requiredValues heap →
      PassCapacity bits kept requiredValues (advanceHeap middle heap) memo

/-- Initial domain facts and numeric earlier-prefix plans derive all existing stage checks. -/
theorem ranges (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (records : List SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (capacity : StageCapacity bits budget records values before fourth memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    SourceCurrentConjunctionScanClassPass.Ranges budget records values before fourth memo := by
  have pathsProper : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, ∀ path ∈ paths, path ≠ [] := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact proper record present
  have pathsActive : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, Nontrivial paths := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact (fields record present).2.2
  have scanRanges := SourceCurrentAllocatedFiniteOrdinaryScanRanges.scan_ranges budget sourceGate sourceReaches values
    (records.map SourceEqualityClassOrder.Record.paths) before fourth ready.good.native.machine.1.coherent available domain
  refine ⟨scanRanges, ?_⟩
  intro selected middle savedFourth actual kept retained fuel readFuel requiredValues heap required
  have unchanged := (SourceCurrentAllocatedFiniteOrdinaryScan.scan actual ready available domain).2.2.1
  subst middle
  obtain ⟨requiredInventory, receipt⟩ := SourceCurrentConjunctionRequiredActual.verified formulas solver inventory actual
    ready admitted available pathsProper pathsActive correct scanRanges required
  have narrowed := SourceCurrentAllocatedFiniteOrdinaryRequired.requireAll_done fuel readFuel
    (SourceEqualitySelectedRequired.paths selected) values requiredValues before.native.machine.heap heap
    required ready.semantic available domain
  obtain ⟨nextMemos, _reads, nextValid, _unfolding, _query⟩ := SourceCurrentRequiredQueryMemos.requireAll_memos
    fuel readFuel (SourceEqualitySelectedRequired.paths selected) values requiredValues before.native.machine.heap heap
    required ready.semantic ready.costs available memos valid
  have currentNative : NativeStored (advanceHeap before heap).native :=
    SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored before.native _ native
  have retainedFields := retained.fields
  exact SourceCurrentAllocatedFiniteOrdinaryPassCapacity.ranges bits formulas solver requiredInventory kept requiredValues
    (advanceHeap before heap) memo
    (fun record member => (fields record (retainedFields.1.subset member)).1)
    (fun record member => (fields record (retainedFields.1.subset member)).2.2)
    receipt.ready receipt.admitted receipt.resident narrowed.2.2.2.1
    (physical.grows receipt.effects.keeps) covered currentNative merged
    (capacity.pass actual kept retained fuel readFuel requiredValues heap required) nextMemos nextValid

/-- Numeric earlier-prefix plans construct the complete actual stage and positional bounds. -/
theorem finite (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (records : List SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (capacity : StageCapacity bits budget records values before fourth memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ outcome results after savedFourth saved next final,
      ∃ actual : Reduction budget records values before fourth memo outcome results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next records values results before after fourth savedFourth memo saved outcome final ∧
        NativeStored after.native ∧ MergeStored saved ∧
        All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results := by
  have checks := ranges bits formulas solver inventory budget records values before fourth memo ready admitted available domain
    proper fields correct physical covered native merged capacity memos valid
  obtain ⟨outcome, results, after, savedFourth, saved, next, final, actual, reads, receipt⟩ :=
    SourceCurrentConjunctionScanClassPassActual.finite formulas solver inventory budget records values before fourth memo ready
      admitted available proper fields correct physical covered checks memos valid
  have structural := SourceCurrentAllocatedFiniteOrdinaryStage.structure_from_reads formulas solver inventory reads ready admitted
    available domain proper fields correct physical covered checks.scan native merged valid
  exact ⟨outcome, results, after, savedFourth, saved, next, final, actual, reads, receipt, structural⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageCapacity
