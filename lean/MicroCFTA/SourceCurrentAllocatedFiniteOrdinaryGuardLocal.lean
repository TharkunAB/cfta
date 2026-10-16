import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardClassPass
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardRequired
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParent
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryScanRanges

/-!
# Hereditary guards through actual local reductions

The ordinary Scan retains its full state and fourth memo.
Required paths retain each input guard vector.
The actual class pass derives its guards before the local return.
The initial raw own vector bounds the sum of class steps.
No future range plan, guard profile, or completed body is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardLocal
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "Bounds" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds
local notation "Children" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children
local notation "NativeGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored
local notation "MergeGuards" => SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "raw" => SourceEqualityConjoinAllocation.readback
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- The own vector bounds class steps. The forest vector bounds their input guards. -/
def outputLimit (ownLimits inputLimits : Limits) : Limits :=
  SourceCurrentAllocatedFiniteOrdinaryGuardTarget.foldLimit inputLimits
    (2 * SourceCurrentAllocatedFiniteOrdinaryGuardOwn.classBudget ownLimits)

/-- The actual Scan, Required, and Pass derive guards at the same complete return. -/
theorem stage
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
    (native : NativeStored before.native) (merged : MergeStored memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (guards : NativeGuards before.native) (mergeGuards : MergeGuards memo)
    (limits : Limits) (profile : Children limits values) :
    MergeGuards saved ∧ NativeGuards after.native ∧
      Children (SourceCurrentAllocatedFiniteOrdinaryGuardClassPass.passLimit limits records) results := by
  have domain := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.domain values profile
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
      have guardsAfter : NativeGuards (advanceHeap before heap).native :=
        SourceCurrentAllocatedFiniteOrdinaryGuardStored.advance_stored before.native _ guards
      have requiredProfile := SourceCurrentAllocatedFiniteOrdinaryGuardRequired.requireAll_done fuel readFuel
        (SourceEqualitySelectedRequired.paths selected) values requiredValues before.native.machine.heap heap
        required ready.semantic available limits profile
      have retainedFields := retained.fields
      exact SourceCurrentAllocatedFiniteOrdinaryGuardClassPass.pass formulas solver requiredInventory last
        (fun record member => (fields record (retainedFields.1.subset member)).1)
        (fun record member => (fields record (retainedFields.1.subset member)).2.2)
        requiredReceipt.ready requiredReceipt.admitted requiredReceipt.resident narrowed.2.2.2.1
        (physicalStored.grows requiredReceipt.effects.keeps) covered nativeAfter merged requiredValid guardsAfter mergeGuards limits requiredProfile

/-- Actual local reads derive their output vector from the initial own guard and forest. -/
theorem local_reads
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
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (guards : NativeGuards before.native) (mergeGuards : MergeGuards memo)
    (ownLimits inputLimits : Limits) (ownBound : Bounds ownLimits original) (profile : Children inputLimits values) :
    MergeGuards saved ∧ NativeGuards after.native ∧ Children (outputLimit ownLimits inputLimits) results := by
  cases reads with
  | unchanged =>
      exact ⟨mergeGuards, guards, SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.mono _ profile
        (SourceCurrentAllocatedFiniteOrdinaryGuardTarget.foldLimit_ge _ _)⟩
  | emptyChildren =>
      refine ⟨mergeGuards, guards, SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.children_of_members _ _ ?_⟩
      intro value member
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      trivial
  | classes read =>
      rename_i records outcome actual continuation
      obtain ⟨own, checked⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory before
        original loaded inherited ready admitted cached found inheritedReady actual
      obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
      have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
        intro record member
        exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      have bounds := stage formulas solver inventory read checked.ready checked.admitted available
        recordsProper fields correct physicalStored covered native merged valid guards mergeGuards inputLimits profile
      have steps := SourceCurrentAllocatedFiniteOrdinaryGuardOwn.receipt_steps checked ownLimits ownBound
      exact ⟨bounds.1, bounds.2.1, SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.mono _ bounds.2.2
        (SourceCurrentAllocatedFiniteOrdinaryGuardClassPass.passLimit_le_count inputLimits records _ steps)⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardLocal
