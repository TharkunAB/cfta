import MicroCFTA.SourcePruningEnumerationParentProjectionScan
import MicroCFTA.SourcePruningEnumerationParentProjectionEdits
import MicroCFTA.SourceCurrentAllocatedLocalWorkerActual
import MicroCFTA.SourceCurrentAllocatedParentEdgeActual
import MicroCFTA.SourcePruningEnumerationCheckedProjectionHeap

/-!
# Whole projectability through actual local reduction and parent construction

This draft follows the actual recorded worker endpoints.
It does not assert completion of an arbitrary native prefix.
-/
namespace MicroCFTA.SourcePruningEnumerationLocalReductionProjectionHeap
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "unconstrained" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

private theorem continuation_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {records : List SourceEqualityClassOrder.Record}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {outcome : Option Class} {memos final : Memos}
    {actual : SourceCurrentConjunctionScanClassPass.Reduction budget records values before fourth memo
      outcome results after savedFourth saved}
    (reads : SourceCurrentConjunctionScanClassPassActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values
      (records.map SourceEqualityClassOrder.Record.paths) before fourth)
    (valid : Valid before.native.machine.heap memos) (heap : Heap before.native.machine.heap) :
    Heap after.native.machine.heap := by
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
      exact SourcePruningEnumerationScanProjectionHeap.scan_heap formulas solver scan ready available pathsProper correct ranges heap
  | completed first second last =>
      rename_i kept requiredValues middle selected returnedHeap fuel readFuel scanMemos requiredMemos required scan retained pass
      obtain ⟨scanInventory, scanReady, scanAdmitted, scanEffects, scanValues, scanCorrect, fourthRetained, _⟩ :=
        SourceCurrentConjunctionClassScanSoundness.verified formulas solver inventory scan ready admitted available
          pathsProper pathsActive correct ranges
      have scanValid := (SourceCurrentAllocatedScanReadValidity.scan first ready available pathsProper
        formulas solver correct ranges valid).1
      have scanHeap := SourcePruningEnumerationScanProjectionHeap.scan_heap formulas solver scan
        ready available pathsProper correct ranges heap
      obtain ⟨requiredInventory, requiredReceipt⟩ := SourceCurrentConjunctionRequiredActual.verified
        formulas solver inventory scan ready admitted available pathsProper pathsActive correct ranges required
      have requiredValid := (SourceCurrentAllocatedRequiredReadValidity.required second scanReady.semantic
        scanReady.costs scanValues scanValid).1
      have requiredHeap := (SourceCurrentRequiredHeapEffects.requireAll (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none) fuel readFuel
        (SourceEqualitySelectedRequired.paths selected) values requiredValues middle.native.machine.heap returnedHeap
        required scanReady.semantic scanReady.costs scanHeap scanValues).2.2.2.1
      have retainedFields := retained.fields
      exact SourcePruningEnumerationClassEditProjectionHeap.pass_heap formulas solver requiredInventory last
        (fun record member => (fields record (retainedFields.1.subset member)).1)
        (fun record member => (fields record (retainedFields.1.subset member)).2.2)
        requiredReceipt.ready requiredReceipt.admitted requiredReceipt.resident
        (SourceCurrentConjunctionRequiredClassPass.selected_domains requiredReceipt kept retainedFields.2)
        (stored.grows (scanEffects.keeps.trans requiredReceipt.effects.keeps)) covered requiredValid requiredHeap

/-- Actual local reads preserve projectability under the complete original verified admission. -/
theorem reduction_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : Guard)
    {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : SourceCurrentAllocatedLocalReduction.Reduction budget loaded inherited values before fourth memo
      results after savedFourth saved}
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
    (valid : Valid before.native.machine.heap memos) (heap : Heap before.native.machine.heap) :
    Heap after.native.machine.heap := by
  cases reads with
  | unchanged => exact heap
  | emptyChildren => exact heap
  | classes reads =>
      rename_i records outcome actual continuation
      obtain ⟨own, checked⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified
        formulas solver inventory before original loaded inherited ready admitted cached found inheritedReady actual
      obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
      exact continuation_heap formulas solver inventory reads checked.ready checked.admitted available
        (fun record member => proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)) fields
        correct stored covered (ranges records checked.actual) valid heap

/-- A literal completed worker derives projectability at its own returned checked state. -/
theorem literal_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {original : Guard} {g s r e p h m c n budget : Nat}
    {loaded : Allocated} {inherited : EqValue} {values results : List (Value Symbol Guard)}
    {before : SourceCurrentAllocatedPartialState.State width} {after : Checked width}
    {savedFourth : Fourth} {saved : Memo} {memos : Memos}
    (initial : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory before memos)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (ranges : SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before.checked before.fourth before.merge)
    (done : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values
      before.checked before.fourth before.merge = .done results after savedFourth saved)
    (heap : Heap before.checked.native.machine.heap) : Heap after.native.machine.heap := by
  obtain ⟨next, final, actual, reads, _receipt⟩ := SourceCurrentAllocatedLocalWorkerActual.sound
    formulas solver initial cached found inheritedReady available ranges done
  exact reduction_heap formulas solver inventory original reads initial.ready initial.admitted cached found inheritedReady
    available initial.correct initial.stored initial.covered
    (SourceCurrentAllocatedLocalReductionActual.ranges_of_finite ranges) initial.globals heap

end MicroCFTA.SourcePruningEnumerationLocalReductionProjectionHeap


namespace MicroCFTA.SourcePruningEnumerationParentProjectionHeap
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedParentEdge (Edge)
open SourceCurrentAllocatedParentEdgeActual (Reads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "raw" => SourceEqualityConjoinAllocation.readback
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- The supplied actual parent reads retain projectability at the same returned native heap. -/
theorem parent_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {values : List (Value Symbol Guard)} {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved}
    (reads : Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (live : contradictory original = false →
      SourceEqualityGuardReadback.Cached original.equalities ∧
      SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap values ∧
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) (heap : Heap before.native.machine.heap) :
    Heap after.native.machine.heap := by
  cases reads with
  | rejected =>
      exact SourceCurrentAllocatedMkEdge.reject_projectable_heap _ _ heap
  | live reads =>
      rename_i children middle test built reduction
      obtain ⟨cached, found, inheritedReady, available, ranges⟩ := live test
      have middleHeap := SourcePruningEnumerationLocalReductionProjectionHeap.reduction_heap
        formulas solver inventory original reads ready admitted cached found inheritedReady available
        correct stored covered ranges valid heap
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
        ready.good.operations.constraints cached loaded found
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedLocalReductionActual.verified formulas solver inventory original
        reads ready admitted cached found inheritedReady available correct stored covered ranges valid
      have storedReady := loadedReady.1.grows receipt.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (raw loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.operations original from ⟨cached, loaded, found⟩).grows
          receipt.effects.grows
      obtain ⟨chosen, returned, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver next symbol loaded children middle
        receipt.ready receipt.admitted storedReady field receipt.available
      have same := Prod.mk.inj (constructor.actual.symm.trans built)
      have sameValue := Except.ok.inj same.1
      cases sameValue
      cases same.2
      exact constructor.preserves_projection_heap receipt.ready.good.operations storedReady middleHeap

/-- The full original actual-return receipt is retained at the same endpoint. -/
theorem verified_projection_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {values : List (Value Symbol Guard)} {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved}
    (reads : Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (live : contradictory original = false →
      SourceEqualityGuardReadback.Cached original.equalities ∧
      SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap values ∧
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) (heap : Heap before.native.machine.heap) :
    (∃ next, SourceCurrentAllocatedParentEdge.Receipt formulas solver next symbol original loaded inherited values before result after fourth savedFourth memo saved final) ∧
      Heap after.native.machine.heap := by
  have packet := SourceCurrentAllocatedParentEdgeActual.verified formulas solver inventory reads ready admitted live
    correct stored covered valid
  exact ⟨packet, parent_heap formulas solver inventory reads ready admitted live correct stored covered valid heap⟩

/-- The original finite producer is called once and retains its whole return packet. -/
theorem finite_projection_heap (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentAllocatedParentEdge.Ranges budget original loaded inherited values before fourth memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (heap : Heap before.native.machine.heap) :
    ∃ result after savedFourth saved next final,
      ∃ actual : Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved,
        (Reads formulas solver actual memos final ∧
          SourceCurrentAllocatedParentEdge.Receipt formulas solver next symbol original loaded inherited values before result after fourth savedFourth memo saved final) ∧
        Heap after.native.machine.heap := by
  obtain ⟨result, after, savedFourth, saved, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedParentEdgeActual.finite formulas solver inventory budget symbol original loaded inherited
      values before fourth memo ready admitted cached found inheritedReady available correct stored covered ranges memos valid
  have liveInputs : contradictory original = false →
      SourceEqualityGuardReadback.Cached original.equalities ∧
      SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap values ∧
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth :=
    fun test => ⟨cached, found, inheritedReady, available,
      SourceCurrentAllocatedLocalReductionActual.ranges_of_finite (ranges test)⟩
  exact ⟨result, after, savedFourth, saved, next, final, actual, ⟨reads, receipt⟩,
    parent_heap formulas solver inventory reads ready admitted liveInputs correct stored covered valid heap⟩

end MicroCFTA.SourcePruningEnumerationParentProjectionHeap
