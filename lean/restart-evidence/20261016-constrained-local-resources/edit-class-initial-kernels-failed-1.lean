import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassInitialCapacity
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.maxDepth 1000000
set_option pp.maxSteps 10000000
namespace MicroCFTA.EditClassInitialCapacityChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape RowsShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests observe makeEdge_observe)
open MergedOrdinaryHeight (height edgesHeight childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
open SourceCurrentAllocatedFiniteOrdinaryEditCapacity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}


section Edit
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (bits : Nat) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
variable (rowLimit arity count depth bound inputRows inputArity inputBound : Nat)
local notation "TargetR" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows record rowLimit count depth bound
local notation "OutR" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.outputRows record rowLimit count depth bound inputRows
local notation "OutA" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.outputArity arity inputArity
local notation "LeafN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leafNodes record rowLimit arity count depth bound inputRows inputArity inputBound
local notation "LeafE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leafEdges record rowLimit arity count depth bound inputRows inputArity inputBound
local notation "NN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeNodes LeafN
local notation "NE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeEdges LeafE
local notation "CN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.childrenNodes LeafN
local notation "CE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.childrenEdges LeafE
local notation "RN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.rowsNodes LeafN
local notation "RE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.rowsEdges LeafE


variable (known : Values base originals) (coherent : SourceEqualityClassOrder.Coherent record)
variable (active : EqualityNormalize.Nontrivial record.paths) (captured : ChildrenShape rowLimit arity originals)
variable (lengthBound : originals.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
variable (capturedHeight : childrenHeight originals ≤ bound)
include known coherent active captured lengthBound pathsBound capturedHeight
theorem initial_node_ranges (inventory : Inventory) (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard)
    (before : Shared (bits + 2))
    (ready : Ready formulas solver inventory record originals base before)
    (stored : Stored TargetR (max arity 1) bound before)
    (available : Available before.checked.native.machine.heap value)
    (profile : NodeShape inputRows inputArity value) (heightBound : height value ≤ inputBound)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits) (safe : Safe edits value)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (nodes : before.checked.native.machine.heap.nodes.next + NN value ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + NE value ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedSharedEditRanges.NodeRanges record originals edits value before := by
  have capacity := SourceCurrentAllocatedFiniteOrdinaryEditInitialCapacity.node formulas solver bits record originals base
    rowLimit arity count depth bound inputRows inputArity inputBound known coherent active captured lengthBound pathsBound capturedHeight
    inventory edits value before ready stored available profile heightBound populated nonempty allowed safe memos valid nodes edges
  exact SourceCurrentAllocatedFiniteOrdinaryEditCapacity.node_ranges bits formulas solver record originals base known (ChildrenShape.domain originals captured) coherent active
    capacity populated nonempty allowed inventory ready available safe stored.domain (NodeShape.domain value profile) memos valid

theorem initial_list_ranges (inventory : Inventory) (edits : Edits EqualityNormalize.Path)
    (values : List (Value Symbol Guard)) (before : Shared (bits + 2))
    (ready : Ready formulas solver inventory record originals base before)
    (stored : Stored TargetR (max arity 1) bound before)
    (available : Values before.checked.native.machine.heap values)
    (profile : ChildrenShape inputRows inputArity values) (heightBound : childrenHeight values ≤ inputBound)
    (populated : Populated edits) (allowed : Allowed record edits)
    (safe : SourceCurrentAllocatedSharedEditEffects.ListSafe edits values)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (nodes : before.checked.native.machine.heap.nodes.next + CN values ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + CE values ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedSharedEditRanges.ListRanges record originals edits values before := by
  have capacity := SourceCurrentAllocatedFiniteOrdinaryEditInitialCapacity.list formulas solver bits record originals base
    rowLimit arity count depth bound inputRows inputArity inputBound known coherent active captured lengthBound pathsBound capturedHeight
    inventory edits values before ready stored available profile heightBound populated allowed safe memos valid nodes edges
  exact SourceCurrentAllocatedFiniteOrdinaryEditCapacity.list_ranges bits formulas solver record originals base known (ChildrenShape.domain originals captured) coherent active
    capacity populated allowed inventory ready available safe stored.domain (ChildrenShape.domain values profile) memos valid

end Edit
section Class
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
open SourceCurrentAllocatedFiniteOrdinaryClassResources (nodeBudget edgeBudget)
theorem initial_class_ranges (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) (values : List (Value Symbol Guard))
    (before : Checked (bits + 2)) (memo : Memo) (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget record rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget record rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedClassEdits.ClassRanges record values before memo := by
  have capacity := SourceCurrentAllocatedFiniteOrdinaryClassInitialCapacity.complete formulas solver inventory bits record coherent active values before memo ready admitted available physical profiles native output covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  exact SourceCurrentAllocatedFiniteOrdinaryClassCapacity.class_ranges bits formulas solver inventory record coherent active
    values before memo ready admitted available (ChildrenShape.domain values profile) physical covered native profiles.domain
    capacity memos valid

theorem constructed_class_worker (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) (values : List (Value Symbol Guard))
    (before : Checked (bits + 2)) (memo : Memo) (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget record rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget record rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ results after saved next final,
      ∃ actual : SourceCurrentAllocatedClassEdits.Class record values before memo results after saved,
        SourceCurrentAllocatedClassEdits.ClassReads formulas solver actual memos final ∧
        SourceCurrentAllocatedClassEdits.Receipt formulas solver next record values before memo results after saved memos final ∧
        NativeStored after.native ∧ SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored saved ∧
        All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results ∧
        SourceCurrentAllocatedClassWorkerCompletion.StableRun
          (fun e p h m s n => SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo)
          results after saved := by
  have capacity := SourceCurrentAllocatedFiniteOrdinaryClassInitialCapacity.complete formulas solver inventory bits record coherent active values before memo ready admitted available physical profiles native output covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  obtain ⟨results, after, saved, next, final, actual, reads, receipt, finalNative, finalMerged, related⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryClassCapacity.finite bits formulas solver inventory record coherent active
      values before memo ready admitted available (ChildrenShape.domain values profile) physical covered native profiles.domain
      capacity memos valid
  exact ⟨results, after, saved, next, final, actual, reads, receipt, finalNative, finalMerged, related,
    SourceCurrentAllocatedClassWorkerCompletion.class_complete actual⟩

end Class

#print axioms initial_node_ranges
#check @initial_node_ranges

#print axioms initial_list_ranges
#check @initial_list_ranges

#print axioms initial_class_ranges
#check @initial_class_ranges

#print axioms constructed_class_worker
#check @constructed_class_worker
end MicroCFTA.EditClassInitialCapacityChecks
