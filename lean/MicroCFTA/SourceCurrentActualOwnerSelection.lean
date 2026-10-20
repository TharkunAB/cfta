import MicroCFTA.SourceCurrentActualParentBranchCases
import MicroCFTA.SourceCurrentSelectedPrimaryOrigins
import MicroCFTA.InternedValueMass

/-!
# Selected Parent work for an exact ordinary owner copy

An original direct child has smaller structural mass than its ordinary
owner. Erasure and rejection return Empty. An exact owner copy therefore
comes from the selected Parent branch. Its retained records have false
primary traces on the original child forest at the same Scan return heap.
No gate is assumed on the prepared or edited forest.
-/
namespace MicroCFTA.SourceCurrentActualOwnerSelection
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentMemoMergeEffects (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
variable {width : Nat}

private theorem prefix_good {loaded : Allocated} {inherited : SourceEqualityConstraintAllocation.Value}
    {original : Guard} {before : Checked width} (good : Good before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : EqReady before.operations.constraints inherited) :
    Good (prefixState before loaded inherited) := by
  have ready := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
    good.operations.constraints cached loaded found
  have constructor := SourceEqualityConstraintFieldLookup.load_constructor_receipt original
    before.operations.constraints cached loaded found
  obtain ⟨_, _, _, _, _, valid, growth⟩ :=
    SourceEqualityPartialPrecheckAllocation.run_correct loaded.stored loaded.guard inherited before.operations
      good.operations ready.1 inheritedReady original.equalities cached constructor
  have effects : SourceCurrentConjunctionRowsAllocation.Effects (SourceCurrentAllocatedNativeEffects.physical before)
      ⟨before.native.machine.heap,
        (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).2⟩ :=
    ⟨SourceEqualityRequiredCache.pure_keeps _ good.heap,
      ⟨good.semantic, good.costs, valid, good.fields.grows growth⟩, growth⟩
  exact good.advance _ effects

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- An exact owner copy retains selected work and every original false primary gate. -/
theorem selected {g s r e p h m c n budget inherited before fourth memo returned after saved current}
    {ownerEntry ownerDepth ownerFree} {ownerRows : List (EdgeValue Symbol Guard)}
    {row : EdgeValue Symbol Guard} {index : Nat}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget row.entry.key.symbol
      row.entry.key.constraint inherited row.children before fourth memo = .done returned after saved current)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (live : SourceEqualityMkEdgeAllocation.contradictory row.entry.key.constraint = false →
      FieldAvailable before.operations row.entry.key.constraint ∧ EqReady before.operations.constraints inherited ∧
        Values before.native.machine.heap row.children)
    (member : row ∈ ownerRows)
    (found : returned.children[index]? = some (.node ownerEntry ownerRows ownerDepth ownerFree)) :
    ∃ (loaded : Allocated) (middle : Checked width) (records kept : List Record)
      (scanned : Checked width) (scanFourth : Fourth) (prepared : List Node) (preparedHeap : Heap),
      SourceEqualityMkEdgeAllocation.contradictory row.entry.key.constraint = false ∧
      SourceEqualityConstraintFieldLookup.load row.entry.key.constraint before.operations.constraints = .ok (some loaded) ∧
      SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited row.children
        before fourth memo = .done returned.children middle saved current ∧
      SourceCurrentAllocatedMkEdge.build row.entry.key.symbol loaded returned.children middle = (.ok returned, after) ∧
      SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded)
        returned.children.length = true ∧
      (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 =
        .ok (.classes records) ∧
      SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget row.children records
        (prefixState before loaded inherited) fourth = .done (none, kept) scanned scanFourth ∧
      kept ≠ [] ∧
      SourceEqualityRequiredExecution.requireAll r h
        (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) row.children
        scanned.native.machine.heap = .done prepared preparedHeap ∧
      SourceCurrentAllocatedClassWorker.pass e p h m c n kept prepared
        (advanceHeap scanned preparedHeap) memo = .done returned.children middle current ∧
      saved = scanFourth ∧
      ∀ record ∈ kept, EndpointStatefulGateTrace.ClassTrace source reaches row.children record.paths
        scanned.native.machine.heap false scanned.native.machine.heap := by
  rcases SourceCurrentActualParentBranchCases.edge_cases actual good stored live with original | erased | sentinel | selected
  · have inside : (.node ownerEntry ownerRows ownerDepth ownerFree : Node) ∈ row.children := by
      rw [original] at found
      exact List.mem_of_getElem? found
    exact False.elim (Nat.lt_irrefl _ (InternedValueMass.node_child_lt ownerEntry ownerRows ownerDepth ownerFree
      row member (.node ownerEntry ownerRows ownerDepth ownerFree) inside))
  · have inside := List.mem_of_getElem? found
    rw [erased] at inside
    obtain ⟨_, _, impossible⟩ := List.mem_map.mp inside
    cases impossible
  · have inside := List.mem_of_getElem? found
    rw [sentinel] at inside
    cases List.mem_singleton.mp inside
  · obtain ⟨loaded, middle, records, kept, scanned, scanFourth, prepared, preparedHeap,
      noncontradictory, loadedAt, reduced, built, accepted, precheck, scanCall, nonempty,
      requiredCall, passCall, sameFourth⟩ := selected
    obtain ⟨field, inheritedReady, available⟩ := live noncontradictory
    have prefixGood := prefix_good good field.1 loadedAt inheritedReady
    have prefixAvailable : Values (prefixState before loaded inherited).native.machine.heap row.children := available
    have gates := SourceCurrentSelectedPrimaryOrigins.selected_class scanCall prefixGood prefixAvailable
    exact ⟨loaded, middle, records, kept, scanned, scanFourth, prepared, preparedHeap,
      noncontradictory, loadedAt, reduced, built, accepted, precheck, scanCall, nonempty,
      requiredCall, passCall, sameFourth, gates⟩

end MicroCFTA.SourceCurrentActualOwnerSelection
