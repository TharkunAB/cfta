import MicroCFTA.SourceCurrentAllocatedLocalWorkerActual
import MicroCFTA.SourcePruningEnumerationScanArity
import MicroCFTA.SourcePruningEnumerationRequiredArity
import MicroCFTA.SourcePruningEnumerationClassPassArity

/-!
# Arity through actual local equality reduction

The real precheck selects the continuation.
Scan, required children and class edits use their exact returned states.
Each phase derives arity for every record that it creates.
-/
namespace MicroCFTA.SourcePruningEnumerationLocalReductionArity
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (Ready)
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
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
      exact SourcePruningEnumerationScanArity.scan_heap formulas solver scan ready available pathsProper correct ranges heap
  | completed first second last =>
      rename_i kept requiredValues middle selected returnedHeap fuel readFuel scanMemos requiredMemos required scan retained pass
      obtain ⟨scanInventory, scanReady, scanAdmitted, scanEffects, scanValues, scanCorrect, fourthRetained, _⟩ :=
        SourceCurrentConjunctionClassScanSoundness.verified formulas solver inventory scan ready admitted available
          pathsProper pathsActive correct ranges
      have scanValid := (SourceCurrentAllocatedScanReadValidity.scan first ready available pathsProper
        formulas solver correct ranges valid).1
      have scanHeap := SourcePruningEnumerationScanArity.scan_heap formulas solver scan
        ready available pathsProper correct ranges heap
      obtain ⟨requiredInventory, requiredReceipt⟩ := SourceCurrentConjunctionRequiredActual.verified
        formulas solver inventory scan ready admitted available pathsProper pathsActive correct ranges required
      have requiredValid := (SourceCurrentAllocatedRequiredReadValidity.required second scanReady.semantic
        scanReady.costs scanValues scanValid).1
      have requiredHeap := (SourcePruningEnumerationRequiredArity.requireAll fuel readFuel
        (SourceEqualitySelectedRequired.paths selected) values requiredValues middle.native.machine.heap returnedHeap
        required scanReady.semantic scanReady.costs scanHeap scanValues).2.2.2.1
      have retainedFields := retained.fields
      exact SourcePruningEnumerationClassEditArity.pass_heap formulas solver requiredInventory last
        (fun record member => (fields record (retainedFields.1.subset member)).1)
        (fun record member => (fields record (retainedFields.1.subset member)).2.2)
        requiredReceipt.ready requiredReceipt.admitted requiredReceipt.available
        (SourceCurrentConjunctionRequiredClassPass.selected_domains requiredReceipt kept retainedFields.2)
        (stored.grows (scanEffects.keeps.trans requiredReceipt.effects.keeps)) covered requiredValid requiredHeap

/-- Actual local reads preserve arity under the complete original verified admission. -/
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

/-- A literal completed worker derives arity at its own returned checked state. -/
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

end MicroCFTA.SourcePruningEnumerationLocalReductionArity
