import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditCapacity

namespace MicroCFTA.EditCapacityKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditEffects
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryShared.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

theorem numeric_node_execution (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
    (known : Values base originals) (capturedDomain : DChildren originals)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard) (before : SharedState (bits + 2))
    (capacity : SourceCurrentAllocatedFiniteOrdinaryEditCapacity.NodeCapacity bits record originals edits value before)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : SourceCurrentAllocatedSharedTargetState.Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap value) (safe : Safe edits value)
    (stored : Stored before) (domain : DNode value) (memos : EndpointMemoGateTrace.Memos)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) :
    ∃ result after next final, ∃ actual : EditNode record originals edits value before result after,
      NodeReads formulas solver base actual memos final ∧
      NodeReceipt formulas solver next record originals base value before result after memos final ∧
      Stored after ∧ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow value result ∧
      SourceCurrentAllocatedSharedEditWorkerCompletion.StableRun
        (fun e p h m s n => SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n edits value before)
        result after := by
  have ranges := SourceCurrentAllocatedFiniteOrdinaryEditCapacity.node_ranges bits formulas solver record originals base
    known capturedDomain coherent active capacity populated nonempty allowed inventory ready available safe stored domain memos valid
  have domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) originals :=
    fun path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.checked.semantic originals
      (fun value member => ready.captured.available value (known value member)) capturedDomain _
  obtain ⟨result, after, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedSharedEditComplete.node_complete formulas solver record originals base known domains coherent active
      inventory ranges populated nonempty allowed ready available safe memos valid
  have structural := SourceCurrentAllocatedFiniteOrdinaryEdits.node reads populated nonempty allowed ready available safe valid
    known capturedDomain stored domain
  exact ⟨result, after, next, final, actual, reads, receipt, structural.1, structural.2,
    SourceCurrentAllocatedSharedEditWorkerCompletion.node_complete actual⟩

theorem ignored_list_root (bits : Nat) (record : SourceEqualityClassOrder.Record)
    (originals values : List (Value Symbol Guard)) (target : EqualityNormalize.Path) (before : SharedState (bits + 2)) :
    SourceCurrentAllocatedFiniteOrdinaryEditCapacity.ListCapacity bits record originals (.editAt target) values before ∧
      ∀ e p h m s n, SourceCurrentAllocatedSharedEditWorker.editList
        (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n) (.editAt target) values before =
          .done values before := ⟨True.intro, by intros; rfl⟩

#check @numeric_node_execution
#print axioms numeric_node_execution
#check @ignored_list_root
#print axioms ignored_list_root
end MicroCFTA.EditCapacityKernels
