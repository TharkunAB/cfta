import MicroCFTA.SourceCurrentAllocatedProbeParent
import MicroCFTA.SourceCurrentAllocatedParentEdgeActual

/-!
# Filtered probes at supplied strict current returns

The read annotations fix the actual stage, local, and parent execution.
The proofs use those literal intermediate heaps and global bundles.
No different finite return or completed memo schedule is substituted.
-/
namespace MicroCFTA
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "u" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches u
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

namespace SourceCurrentAllocatedProbeReduction
/-- The supplied strict stage reads preserve probes at their own returned heap. -/
theorem stage_heap
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
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget u reaches values
      (records.map SourceEqualityClassOrder.Record.paths) before fourth)
    (valid : Valid before.native.machine.heap memos) (probes : ProbeHeap before.native.machine.heap) :
    ProbeHeap after.native.machine.heap := by
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
      exact SourceCurrentAllocatedProbeScan.scan_heap formulas solver inventory scan ready admitted available
        pathsProper correct ranges probes
  | completed first second last =>
      rename_i kept requiredValues middle selected heap fuel readFuel scanMemos requiredMemos required scan retained pass
      have middleProbes := SourceCurrentAllocatedProbeScan.scan_heap formulas solver inventory scan ready admitted available
        pathsProper correct ranges probes
      obtain ⟨scanInventory, scanReady, scanAdmitted, scanEffects, scanValues, scanCorrect, fourthRetained, _⟩ :=
        SourceCurrentConjunctionClassScanSoundness.verified formulas solver inventory scan ready admitted available
          pathsProper pathsActive correct ranges
      have scanValid := (SourceCurrentAllocatedScanReadValidity.scan first ready available pathsProper
        formulas solver correct ranges valid).1
      obtain ⟨requiredInventory, requiredReceipt⟩ := SourceCurrentConjunctionRequiredActual.verified
        formulas solver inventory scan ready admitted available pathsProper pathsActive correct ranges required
      have requiredProbes := (SourceCurrentAllocatedProbeRequired.requireAll fuel readFuel _ values requiredValues
        middle.native.machine.heap heap required scanReady.semantic scanReady.costs middleProbes scanValues).2.2.2.1
      have requiredValid := (SourceCurrentAllocatedRequiredReadValidity.required second scanReady.semantic
        scanReady.costs scanValues scanValid).1
      have retainedFields := retained.fields
      exact SourceCurrentAllocatedProbeClassPass.pass_heap formulas solver requiredInventory last
        (fun record member => (fields record (retainedFields.1.subset member)).1)
        (fun record member => (fields record (retainedFields.1.subset member)).2.2)
        requiredReceipt.ready requiredReceipt.admitted requiredReceipt.resident
        (SourceCurrentConjunctionRequiredClassPass.selected_domains requiredReceipt kept retainedFields.2)
        (stored.grows (scanEffects.keeps.trans requiredReceipt.effects.keeps)) covered requiredValid requiredProbes
end SourceCurrentAllocatedProbeReduction

namespace SourceCurrentAllocatedProbeParent
/-- The supplied actual precheck branch and continuation retain their literal probe heap. -/
theorem local_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : Guard)
    {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : SourceCurrentAllocatedLocalReduction.Reduction budget loaded inherited values before fourth memo results after savedFourth saved}
    (reads : SourceCurrentAllocatedLocalReductionActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth)
    (valid : Valid before.native.machine.heap memos) (probes : ProbeHeap before.native.machine.heap) :
    ProbeHeap after.native.machine.heap := by
  cases reads with
  | unchanged => exact probes
  | emptyChildren => exact probes
  | classes reads =>
      rename_i records outcome actual continuation
      obtain ⟨own, checked⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory
        before original loaded inherited ready admitted cached found inheritedReady actual
      obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
      have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
        intro record member
        exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      exact SourceCurrentAllocatedProbeReduction.stage_heap formulas solver inventory reads checked.ready checked.admitted
        available recordsProper fields correct stored covered (ranges records checked.actual) valid probes

/-- Supplied parent reads preserve probes without replacing the actual checked return. -/
theorem parent_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {values : List (Value Symbol Guard)} {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : SourceCurrentAllocatedParentEdge.Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved}
    (reads : SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false →
      SourceEqualityGuardReadback.Cached original.equalities ∧
      SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap values ∧
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) (probes : ProbeHeap before.native.machine.heap) :
    ProbeHeap after.native.machine.heap := by
  cases reads with
  | rejected => exact reject_heap _ _ probes
  | live reads =>
      rename_i children middle test built reduction
      obtain ⟨cached, found, inheritedReady, available, ranges⟩ := live test
      have middleProbes := local_heap formulas solver inventory original reads ready admitted cached found inheritedReady
        available correct stored covered ranges valid probes
      have finalProbes := mkEdge_heap symbol loaded children middle middleProbes
      simpa only [built] using finalProbes
end SourceCurrentAllocatedProbeParent
end MicroCFTA
