import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPassProfiles
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParent
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryScanRanges

/-!
# Strong lower profile stores through actual constrained parents

The ordinary Scan retains its complete entry state. Required paths grow
the constructor heap without changing native cells. The actual class pass
retains both strong profile stores at that return. Local prechecks and
parent constructors use their literal operation states. No numeric
headroom, future profile, or recursive callback law is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentProfiles
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
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "raw" => SourceEqualityConjoinAllocation.readback
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- The actual Scan, Required, and Pass retain the exact returned strong stores. -/
theorem stage_profiles
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {records : List SourceEqualityClassOrder.Record}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {outcome : Option Class} {memos final : Memos}
    {actual : SourceCurrentConjunctionScanClassPass.Reduction budget records values before fourth memo outcome results after savedFourth saved}
    (reads : SourceCurrentConjunctionScanClassPassActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo) (output : OutputStored before.native)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    Profiles saved ∧ OutputStored after.native := by
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
      have sameMiddle := (SourceCurrentAllocatedFiniteOrdinaryScan.scan scan ready available domain).2.2.1
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
      have retainedFields := retained.fields
      exact SourceCurrentAllocatedFiniteOrdinaryClassPassProfiles.pass formulas solver requiredInventory last
        (fun record member => (fields record (retainedFields.1.subset member)).1)
        (fun record member => (fields record (retainedFields.1.subset member)).2.2)
        requiredReceipt.ready requiredReceipt.admitted requiredReceipt.resident narrowed.2.2.2.1
        (physicalStored.grows requiredReceipt.effects.keeps) covered nativeAfter profiles requiredValid outputAfter

/-- Actual early prechecks and the live stage retain their complete lower stores. -/
theorem local_profiles
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
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo) (output : OutputStored before.native)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    Profiles saved ∧ OutputStored after.native := by
  cases reads with
  | unchanged => exact ⟨profiles, output⟩
  | emptyChildren => exact ⟨profiles, output⟩
  | classes read =>
      rename_i records outcome actual continuation
      obtain ⟨own, checked⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory before
        original loaded inherited ready admitted cached found inheritedReady actual
      obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
      have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
        intro record member
        exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      exact stage_profiles formulas solver inventory read checked.ready checked.admitted available domain
        recordsProper fields correct physicalStored covered native profiles output valid

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
private theorem constructor_output
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {before after : Checked width} {result : EdgeValue Symbol Guard}
    (receipt : SourceCurrentAllocatedMkEdge.PhysicalReceipt formulas solver inventory before result after)
    (output : OutputStored before.native) : OutputStored after.native :=
  ⟨by simpa only [receipt.nodes] using output.nodes, by simpa only [receipt.edges] using output.edges⟩

/-- Supplied parent reads derive strong stores at the same exact returned constructor state. -/
theorem structure_from_reads
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : EdgeValue Symbol Guard)
    {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : SourceCurrentAllocatedParentEdge.Edge budget original.entry.key.symbol original.entry.key.constraint
      loaded inherited original.children before fourth memo result after savedFourth saved}
    (reads : SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (live : contradictory original.entry.key.constraint = false →
      SourceEqualityGuardReadback.Cached original.entry.key.constraint.equalities ∧
      SourceEqualityConstraintFieldLookup.load original.entry.key.constraint before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap original.children)
    (domain : DEdge original)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo) (output : OutputStored before.native)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      SourceCurrentAllocatedFiniteOrdinaryRequired.EdgeNarrow original result := by
  have ranges : ∀ test : contradictory original.entry.key.constraint = false,
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited original.children before fourth := by
    intro test records _
    exact SourceCurrentAllocatedFiniteOrdinaryScanRanges.scan_ranges budget sourceGate sourceReaches original.children
      (records.map SourceEqualityClassOrder.Record.paths) (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth
      ready.good.native.machine.1.coherent (live test).2.2.2 domain
  have structural := SourceCurrentAllocatedFiniteOrdinaryParent.structure_from_reads formulas solver inventory original reads
    ready admitted (fun test => ⟨(live test).1, (live test).2.1, (live test).2.2.1, (live test).2.2.2, ranges test⟩)
    domain correct physicalStored covered native profiles.domain valid
  have retained : Profiles saved ∧ OutputStored after.native := by
    cases reads with
    | rejected =>
        have constructor := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory
          original.entry.key.symbol before ready admitted
        exact ⟨profiles, constructor_output constructor.toPhysicalReceipt output⟩
    | live reads =>
        rename_i children middle test built reduction
        obtain ⟨cached, found, inheritedReady, available⟩ := live test
        have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original.entry.key.constraint
          before.operations.constraints ready.good.operations.constraints cached loaded found
        have retained := local_profiles formulas solver inventory original.entry.key.constraint reads ready admitted
          cached found inheritedReady available domain correct physicalStored covered native profiles output valid
        obtain ⟨next, receipt⟩ := SourceCurrentAllocatedLocalReductionActual.verified formulas solver inventory
          original.entry.key.constraint reads ready admitted cached found inheritedReady available correct physicalStored
          covered (ranges test) valid
        have storedReady := loadedReady.1.grows receipt.effects.grows.constraint_growth
        have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (raw loaded) := by
          rw [loadedReady.2]
          exact (show SourceCurrentConjunctionEquality.FieldAvailable before.operations original.entry.key.constraint from
            ⟨cached, loaded, found⟩).grows receipt.effects.grows
        obtain ⟨chosen, returned, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver next
          original.entry.key.symbol loaded children middle receipt.ready receipt.admitted storedReady field receipt.available
        have same := Prod.mk.inj (constructor.actual.symm.trans built)
        have sameValue := Except.ok.inj same.1
        cases sameValue
        cases same.2
        exact ⟨retained.1, constructor_output constructor.toPhysicalReceipt retained.2⟩
  exact ⟨structural.1, retained.2, retained.1, structural.2.2⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentProfiles
