import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassInitialCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageInitialCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalInitialCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentResources
import MicroCFTA.SourceCurrentAllocatedParentWorkerStability
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentInitialCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalResources
import MicroCFTA.SourceCurrentAllocatedLocalWorkerStability
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocal
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentCallerResources
import MicroCFTA.SourceCurrentAllocatedParentWorkerActual

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option format.width 180

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
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

set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms initial_node_ranges
#check @initial_node_ranges

set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms initial_list_ranges
#check @initial_list_ranges

set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms initial_class_ranges
#check @initial_class_ranges

set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms constructed_class_worker
#check @constructed_class_worker
end MicroCFTA.EditClassInitialCapacityChecks


namespace MicroCFTA.PassInitialChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Fold Pass PassReads Receipt)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryPassResources (nodeBudget edgeBudget outputRows outputArity)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "PassCapacity" => SourceCurrentAllocatedFiniteOrdinaryPassCapacity.PassCapacity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]


/-- Raw empty tails keep the complete checked state and Merge memo. -/
theorem raw_empty_tail {width : Nat} (values results : List (Value Symbol Guard))
    (before after : Checked width) (memo saved : Memo)
    (actual : Fold [] values before memo results after saved) :
    results = values ∧ after = before ∧ saved = memo := by
  exact SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity.fold_unique actual .nil

/-- Every raw earlier tail receives the head plan at its exact full return. -/
theorem reached_head (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (records : List Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2))
    (record : Record) (present : records = record :: records.tail)
    (middle : List (Value Symbol Guard)) (after : Checked (bits + 2)) (saved : Memo)
    (actualTail : Fold records.tail values before memo middle after saved) :
    SourceCurrentAllocatedFiniteOrdinaryClassCapacity.ClassCapacity bits record middle after saved := by
  have capacity := SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity.complete formulas solver inventory bits records coherent active values before memo
    ready admitted available physical profiles native output covered memos valid rows arity count depth bound
    profile lengthBound pathsBound heightBound nodes edges
  rw [present] at capacity
  exact capacity.head (by simpa only [List.tail_cons] using actualTail)

/-- Initial-only headroom constructs both old ranges and the full current pass receipt. -/
theorem ranges_and_return (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (records : List Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedClassPass.Ranges records values before memo ∧
    ∃ results after saved next final, ∃ actual : Pass records values before memo results after saved,
      PassReads formulas solver actual memos final ∧
      Receipt formulas solver next records values before memo results after saved memos final ∧
      At formulas solver next after ∧ Valid after.native.machine.heap final ∧
      NativeStored after.native ∧ MergeStored saved ∧
      All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results := by
  have checks := SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity.ranges formulas solver inventory bits records coherent active
    values before memo ready admitted available physical profiles native output covered memos valid rows arity count depth bound
    profile lengthBound pathsBound heightBound nodes edges
  obtain ⟨results, after, saved, next, final, actual, reads, receipt, nativeAfter, merged, related⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity.finite formulas solver inventory bits records coherent active
      values before memo ready admitted available physical profiles native output covered memos valid rows arity count depth bound
      profile lengthBound pathsBound heightBound nodes edges
  exact ⟨checks, results, after, saved, next, final, actual, reads, receipt, receipt.admitted,
    receipt.globals.valid, nativeAfter, merged, related⟩

end MicroCFTA.PassInitialChecks

set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms MicroCFTA.PassInitialChecks.raw_empty_tail
#check @MicroCFTA.PassInitialChecks.raw_empty_tail

set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms MicroCFTA.PassInitialChecks.reached_head
#check @MicroCFTA.PassInitialChecks.reached_head

set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms MicroCFTA.PassInitialChecks.ranges_and_return
#check @MicroCFTA.PassInitialChecks.ranges_and_return


namespace StageResourceIntegration
open MicroCFTA Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Scan Ready)
open SourceCurrentConjunctionScanClassPass (Reduction Receipt)
open SourceCurrentConjunctionScanClassPassActual (Reads)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryStageResources
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate
private theorem pass_zero (records : List Record) (rows arity depth bound : Nat) :
    SourceCurrentAllocatedFiniteOrdinaryPassResources.nodeBudget records rows arity 0 depth bound = 0 ∧
    SourceCurrentAllocatedFiniteOrdinaryPassResources.edgeBudget records rows arity 0 depth bound = 0 := by
  induction records with
  | nil => exact ⟨rfl, rfl⟩
  | cons record records ih =>
      simp only [SourceCurrentAllocatedFiniteOrdinaryPassResources.nodeBudget,
        SourceCurrentAllocatedFiniteOrdinaryPassResources.edgeBudget,
        SourceCurrentAllocatedFiniteOrdinaryClassResources.nodeBudget,
        SourceCurrentAllocatedFiniteOrdinaryClassResources.edgeBudget, Nat.zero_mul, Nat.add_zero, ih.1, ih.2]
      exact ⟨trivial, trivial⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- A constructed complete stage supplies the next allocation-free Scan at its actual return. -/
theorem stage_then_scan (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (records : List Record) (values : List (Value Symbol Guard))
    (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ results after saved next final requests,
    ∃ actual : Reduction budget records values before fourth memo none results after fourth saved,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next records values results before after fourth fourth memo saved none final ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget records rows arity count depth bound ∧
      edgeRequests requests ≤ edgeBudget records rows arity count depth bound ∧
      ∃ scan : Scan budget sourceGate sourceReaches results (records.map SourceEqualityClassOrder.Record.paths)
        after fourth none (records.map SourceEqualityClassOrder.Record.paths) after fourth,
        SourceCurrentAllocatedScanSourceReads.ScanReads scan final final := by
  obtain ⟨results, after, saved, next, final, requests, actual, reads, receipt, _stable,
    nativeAfter, outputAfter, profilesAfter, produced, _related, _sameLength, _finalHeight,
    trace, nodeCount, edgeCount, capacity, _nodeSupply, _edgeSupply⟩ :=
    complete formulas solver inventory bits budget records values before fourth memo ready admitted available proper fields correct
      physical profiles native output covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  obtain ⟨scan, nextReads⟩ := SourceCurrentAllocatedFiniteOrdinaryScan.construct budget results
    (records.map SourceEqualityClassOrder.Record.paths) after fourth receipt.ready receipt.available
      (ChildrenShape.domain results produced) final
  exact ⟨results, after, saved, next, final, requests, actual, reads, receipt, nativeAfter, outputAfter,
    profilesAfter, capacity, trace, nodeCount, edgeCount, scan, nextReads⟩

/-- An empty forest needs no constructor headroom even with nonempty class records. -/
theorem empty_forest (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (records : List Record) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity depth bound : Nat)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (nodes : before.native.machine.heap.nodes.next ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2)) :
    ∃ after saved next final requests,
    ∃ actual : Reduction budget records [] before fourth memo none [] after fourth saved,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next records [] [] before after fourth fourth memo saved none final ∧
      SourceCurrentAllocatedLocalWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n
          budget records [] before fourth memo) [] after fourth saved ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests = 0 ∧ edgeRequests requests = 0 ∧
      SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next := by
  have zero := pass_zero records rows arity depth bound
  have nodeZero : nodeBudget records rows arity 0 depth bound = 0 := by simp only [nodeBudget, Nat.zero_mul, Nat.zero_add, zero.1]
  have edgeZero : edgeBudget records rows arity 0 depth bound = 0 := by simp only [edgeBudget, Nat.zero_mul, Nat.zero_add, zero.2]
  obtain ⟨results, after, saved, next, final, requests, actual, reads, receipt, stable,
    nativeAfter, outputAfter, profilesAfter, _produced, _related, sameLength, _finalHeight,
    trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply⟩ :=
    complete formulas solver inventory bits budget records [] before fourth memo ready admitted (by simp [Values]) proper fields correct
      physical profiles native output covered memos valid rows arity 0 depth bound (by trivial) (by simp) pathsBound
      (by change 0 ≤ bound; omega) (by simpa only [nodeZero, Nat.add_zero] using nodes) (by simpa only [edgeZero, Nat.add_zero] using edges)
  have resultsEmpty : results = [] := List.length_eq_zero_iff.mp sameLength
  subst results
  rw [nodeZero] at nodeCount nodeSupply
  rw [edgeZero] at edgeCount edgeSupply
  exact ⟨after, saved, next, final, requests, actual, reads, receipt, stable, nativeAfter, outputAfter,
    profilesAfter, trace, Nat.eq_zero_of_le_zero nodeCount, Nat.eq_zero_of_le_zero edgeCount, capacity,
    by simpa only [Nat.add_zero] using nodeSupply, by simpa only [Nat.add_zero] using edgeSupply⟩

set_option pp.explicit true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 100000
set_option format.width 200
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms stage_then_scan
#check @stage_then_scan
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms empty_forest
#check @empty_forest
end StageResourceIntegration


namespace StageInitialIntegration
open MicroCFTA Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Scan Ready advanceHeap)
open SourceCurrentConjunctionSelectedRecords (Retained)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryStageResources (nodeBudget edgeBudget)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial budgets cover every actual earlier Required return and derive the old stage checks. -/
theorem arbitrary_earlier_required (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (records : List Record) (values : List (Value Symbol Guard))
    (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : SourceCurrentAllocatedFiniteOrdinaryStored.Stored before.native)
    (output : SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2))
    {selected : Constraints} {middle : Checked (bits + 2)} {savedFourth : Fourth}
    (scan : Scan budget sourceGate sourceReaches values (records.map SourceEqualityClassOrder.Record.paths)
      before fourth none selected middle savedFourth)
    (kept : List Record) (retained : Retained scan records kept) (fuel readFuel : Nat)
    (requiredValues : List (Value Symbol Guard)) (heap : State Symbol Guard)
    (required : SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
      values middle.native.machine.heap = .done requiredValues heap) :
    SourceCurrentAllocatedFiniteOrdinaryPassCapacity.PassCapacity bits kept requiredValues (advanceHeap middle heap) memo ∧
      SourceCurrentConjunctionScanClassPass.Ranges budget records values before fourth memo := by
  have capacity := SourceCurrentAllocatedFiniteOrdinaryStageInitialCapacity.complete formulas solver inventory bits budget
    records values before fourth memo ready admitted available proper fields correct physical profiles native output covered
    memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  refine ⟨capacity.pass scan kept retained fuel readFuel requiredValues heap required, ?_⟩
  exact SourceCurrentAllocatedFiniteOrdinaryStageCapacity.ranges bits formulas solver inventory budget records values
    before fourth memo ready admitted available (ChildrenShape.domain values profile) proper fields correct physical
    covered native profiles.domain capacity memos valid

set_option pp.explicit true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 100000
set_option format.width 200
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms arbitrary_earlier_required
#check @arbitrary_earlier_required
end StageInitialIntegration


namespace MicroCFTA.LocalInitialChecks
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedLocalReduction (Reduction Receipt)
open SourceCurrentAllocatedLocalReductionActual (Reads)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryLocalResources (nodeBudget edgeBudget)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
local notation "LocalCapacity" => SourceCurrentAllocatedFiniteOrdinaryLocalCapacity.LocalCapacity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]


/-- An unchanged actual initial precheck needs no later capacity obligation. -/
theorem early_vacuous (bits budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (unchanged : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .unchanged) :
    LocalCapacity bits budget loaded inherited values before fourth memo := by
  intro records actual
  have impossible := Except.ok.inj (unchanged.symm.trans actual)
  cases impossible

/-- The initial budgets give every actual classes prefix its exact stage capacity plan. -/
theorem reached_classes (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget loaded inherited before.operations rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget loaded inherited before.operations rows arity count depth bound ≤ 2 ^ (bits + 2))
    (records : List SourceEqualityClassOrder.Record)
    (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records)) :
    SourceCurrentAllocatedFiniteOrdinaryStageCapacity.StageCapacity bits budget records values
      (prefixState before loaded inherited) fourth memo := by
  exact (SourceCurrentAllocatedFiniteOrdinaryLocalInitialCapacity.complete formulas solver inventory bits budget original loaded inherited
    values before fourth memo ready admitted cached found inheritedReady available correct physical profiles native output covered
    memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges) records actual

/-- The derived plan constructs the current full local return and global validity. -/
theorem ranges_and_return (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget loaded inherited before.operations rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget loaded inherited before.operations rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo ∧
    ∃ results after savedFourth saved next final,
      ∃ actual : Reduction budget loaded inherited values before fourth memo results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next original loaded inherited values results before after fourth savedFourth memo saved final ∧
        At formulas solver next after ∧ Valid after.native.machine.heap final ∧
        NativeStored after.native ∧ MergeStored saved ∧
        All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results := by
  have checks := SourceCurrentAllocatedFiniteOrdinaryLocalInitialCapacity.ranges formulas solver inventory bits budget original loaded inherited
    values before fourth memo ready admitted cached found inheritedReady available correct physical profiles native output covered
    memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  obtain ⟨results, after, savedFourth, saved, next, final, actual, reads, receipt, nativeAfter, merged, related⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryLocalInitialCapacity.finite formulas solver inventory bits budget original loaded inherited
      values before fourth memo ready admitted cached found inheritedReady available correct physical profiles native output covered
      memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  exact ⟨checks, results, after, savedFourth, saved, next, final, actual, reads, receipt,
    receipt.admitted, receipt.globals, nativeAfter, merged, related⟩

end MicroCFTA.LocalInitialChecks

set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms MicroCFTA.LocalInitialChecks.early_vacuous
#check @MicroCFTA.LocalInitialChecks.early_vacuous

set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms MicroCFTA.LocalInitialChecks.reached_classes
#check @MicroCFTA.LocalInitialChecks.reached_classes

set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms MicroCFTA.LocalInitialChecks.ranges_and_return
#check @MicroCFTA.LocalInitialChecks.ranges_and_return

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
namespace MicroCFTA.ParentResourceIndependentChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedParentEdge (Edge Receipt)
open SourceCurrentAllocatedParentEdgeActual (Reads)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "raw" => SourceEqualityConjoinAllocation.readback
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run

open SourceCurrentAllocatedFiniteOrdinaryParentResources (nodeBudget edgeBudget outputRows outputArity)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
theorem constructed_raw_rejection (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (original : EdgeValue Symbol Guard) (loaded : Allocated) (inherited : EqValue)
    (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (test : contradictory original.entry.key.constraint = true)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) (rows arity : Nat)
    (nodes : before.native.machine.heap.nodes.next ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + 1 ≤ 2 ^ (bits + 2)) :
    let result := (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).1
    let after := (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).2
    ∃ requests, ∃ actual : Edge budget original.entry.key.symbol original.entry.key.constraint loaded inherited
        original.children before fourth memo result after fourth memo,
      Reads formulas solver actual memos memos ∧
      Receipt formulas solver inventory original.entry.key.symbol original.entry.key.constraint loaded inherited
        original.children before result after fourth fourth memo memo memos ∧
      SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
          original.entry.key.symbol original.entry.key.constraint inherited original.children before fourth memo) result after fourth memo ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles memo ∧ EdgeShape rows (max arity 1) result ∧
      EdgeNarrow original result ∧ Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests = 0 ∧ edgeRequests requests = 1 ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 1 ∧
      SourceCurrentAllocatedParentWorker.edge 0 0 0 0 0 0 0 0 0 budget original.entry.key.symbol
        original.entry.key.constraint inherited original.children before fourth memo = .done result after fourth memo ∧
      ∀ ambient term, ¬ InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term := by
  obtain ⟨requests, actual, reads, receipt, stable, finalNative, finalOutput, finalProfiles, produced,
    narrowed, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryParentResources.rejected formulas solver inventory bits budget original loaded inherited before fourth memo ready admitted test correct physical profiles native output covered memos valid rows arity nodes edges
  refine ⟨requests, actual, reads, receipt, stable, finalNative, finalOutput, finalProfiles, produced,
    narrowed, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply, ?_, ?_⟩
  · simp only [SourceCurrentAllocatedParentWorker.edge, test, ↓reduceIte]
  · exact (SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory original.entry.key.symbol before ready admitted).empty
      (SourceEqualityPCSGuard.holds formulas solver)

theorem supplied_success_accounted (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (original : EdgeValue Symbol Guard) (loaded : Allocated) (inherited : EqValue)
    (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.entry.key.constraint.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original.entry.key.constraint before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap original.children)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity original.children)
    (lengthBound : original.children.length ≤ count)
    (pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight original.children ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget original.entry.key.constraint loaded inherited before.operations rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget original.entry.key.constraint loaded inherited before.operations rows arity count depth bound ≤ 2 ^ (bits + 2))
    (g s r e p h m c n : Nat) (result : EdgeValue Symbol Guard) (after : Checked (bits + 2))
    (savedFourth : Fourth) (saved : Memo)
    (done : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget original.entry.key.symbol
      original.entry.key.constraint inherited original.children before fourth memo = .done result after savedFourth saved) :
    savedFourth = fourth ∧ ∃ next final requests,
    ∃ actual : Edge budget original.entry.key.symbol original.entry.key.constraint loaded inherited original.children before fourth memo result after fourth saved,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next original.entry.key.symbol original.entry.key.constraint loaded inherited original.children
        before result after fourth fourth memo saved final ∧
      SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
          original.entry.key.symbol original.entry.key.constraint inherited original.children before fourth memo) result after fourth saved ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      EdgeShape (outputRows original.entry.key.constraint loaded inherited before.operations rows count depth bound)
        (outputArity original.entry.key.constraint loaded inherited before.operations arity count) result ∧
      EdgeNarrow original result ∧ Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget original.entry.key.constraint loaded inherited before.operations rows arity count depth bound ∧
      edgeRequests requests ≤ edgeBudget original.entry.key.constraint loaded inherited before.operations rows arity count depth bound ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget original.entry.key.constraint loaded inherited before.operations rows arity count depth bound ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget original.entry.key.constraint loaded inherited before.operations rows arity count depth bound := by
  obtain ⟨chosen, returned, savedMemo, next, final, requests, actual, reads, receipt, stable, rest⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryParentResources.complete formulas solver inventory bits budget original loaded inherited before fourth memo ready admitted cached found inheritedReady available correct physical profiles native output covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  obtain ⟨G, S, R, E, P, H, M, C, N, exactReturn⟩ := stable
  have constructed := exactReturn G S R E P H M C N
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨rfl, rfl, rfl, rfl⟩ := SourceCurrentAllocatedParentWorkerStability.edge_done_unique done constructed
  exact ⟨rfl, next, final, requests, actual, reads, receipt,
    ⟨G, S, R, E, P, H, M, C, N, exactReturn⟩, rest⟩

set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms constructed_raw_rejection
#check @constructed_raw_rejection
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms supplied_success_accounted
#check @supplied_success_accounted
end MicroCFTA.ParentResourceIndependentChecks

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
namespace MicroCFTA.ParentInitialCapacityChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialState (EdgeRequest advance)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialGraph (EdgeBody)
open SourceCurrentAllocatedPartialSourceReads (EdgeBodyReads)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
open SourceCurrentAllocatedFiniteOrdinaryParentResources (nodeBudget edgeBudget outputRows outputArity)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

open SourceCurrentAllocatedFiniteOrdinaryParentCapacity (ParentCapacity)

local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
theorem every_same_cache_load (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {inventory : Inventory}
    (bits budget : Nat) (request : EdgeRequest) (loaded : Allocated) {before : Caller (bits + 2)}
    {memos : EndpointMemoGateTrace.Memos} (initial : Context formulas solver inventory before memos)
    (found : SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints = .ok (some loaded))
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value)
    (profiles : Profiles before.merge) (native : NativeStored before.checked.native) (output : OutputStored before.checked.native)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity request.value.children)
    (lengthBound : request.value.children.length ≤ count)
    (pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard request.inherited before.checked.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight request.value.children ≤ bound)
    (nodes : before.checked.native.machine.heap.nodes.next + nodeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + edgeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ≤ 2 ^ (bits + 2))
    (live : contradictory request.value.entry.key.constraint = false) (candidate : Allocated)
    (candidateFound : SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints = .ok (some candidate)) :
    SourceCurrentAllocatedFiniteOrdinaryLocalCapacity.LocalCapacity bits budget candidate request.inherited
      request.value.children before.checked before.fourth before.merge := by
  exact SourceCurrentAllocatedFiniteOrdinaryParentInitialCapacity.complete formulas solver bits budget request loaded initial found inherited resident profiles native output rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges live candidate candidateFound

theorem constructed_resident_body (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {inventory : Inventory}
    (bits budget : Nat) (request : EdgeRequest) (loaded : Allocated) {before : Caller (bits + 2)}
    {memos : EndpointMemoGateTrace.Memos} (initial : Context formulas solver inventory before memos)
    (found : SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints = .ok (some loaded))
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value)
    (profiles : Profiles before.merge) (native : NativeStored before.checked.native) (output : OutputStored before.checked.native)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity request.value.children)
    (lengthBound : request.value.children.length ≤ count)
    (pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard request.inherited before.checked.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight request.value.children ≤ bound)
    (nodes : before.checked.native.machine.heap.nodes.next + nodeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + edgeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ result checked savedFourth saved next final,
      SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
          request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
          before.checked before.fourth before.merge) result checked savedFourth saved ∧
      ∃ actual : EdgeBody budget request before result (advance before checked savedFourth saved),
        EdgeBodyReads formulas solver actual memos final ∧
        SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result
          (advance before checked savedFourth saved) final ∧
        Post formulas solver next before (advance before checked savedFourth saved) final := by
  have ranges := SourceCurrentAllocatedFiniteOrdinaryParentInitialCapacity.resident_ranges formulas solver bits budget request loaded initial found inherited resident profiles native output rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  exact SourceCurrentAllocatedParentWorkerActual.resident_finite formulas solver budget request initial inherited resident ranges

set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms every_same_cache_load
#check @every_same_cache_load
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms constructed_resident_body
#check @constructed_resident_body
end MicroCFTA.ParentInitialCapacityChecks


/-!
# Initial resources for local equality reduction

The budget reads the deterministic initial precheck result.
Early branches make no constructor request and retain all warm tables.
A live branch constructs its stage at the same returned operation state.
The original field and inherited payload retain the full existing receipt.
-/
namespace MicroCFTA.LocalParentResourceChecks
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedLocalReduction (Reduction Receipt)
open SourceCurrentAllocatedLocalReductionActual (Reads)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run


variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

theorem constructed_unchanged (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (heightBound : childrenHeight values ≤ bound)
    (branch : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .unchanged)
    (capacity : Capacity bits before) :
    ∃ next final requests,
    ∃ actual : Reduction budget loaded inherited values before fourth memo values
        (prefixState before loaded inherited) fourth memo,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next original loaded inherited values values before
        (prefixState before loaded inherited) fourth fourth memo memo final ∧
      SourceCurrentAllocatedLocalWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n
          budget loaded inherited values before fourth memo) values (prefixState before loaded inherited) fourth memo ∧
      NativeStored (prefixState before loaded inherited).native ∧
      OutputStored (prefixState before loaded inherited).native ∧ Profiles memo ∧
      Trace before.native.machine.heap (prefixState before loaded inherited).native.machine.heap requests ∧
      nodeRequests requests = 0 ∧ edgeRequests requests = 0 := by
  have pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth := by
    intro records actual
    rw [branch] at actual
    cases actual
  obtain ⟨results, after, saved, next, final, requests, actual, reads, receipt, stable,
    finalNative, finalOutput, finalProfiles, _produced, _related, _length, _height, trace, nodes, edges,
    _capacity, _nodeSupply, _edgeSupply⟩ := SourceCurrentAllocatedFiniteOrdinaryLocalResources.complete formulas solver
      inventory bits budget original loaded inherited values before fourth memo ready admitted cached found inheritedReady
      available correct physical profiles native output covered memos valid rows arity count depth bound profile lengthBound
      pathsBound heightBound
      (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.nodeBudget, branch, Nat.add_zero] using capacity.1)
      (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.edgeBudget, branch, Nat.add_zero] using capacity.2)
  obtain ⟨g, s, r, e, p, h, m, c, n, enough⟩ := stable
  have done := enough g s r e p h m c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have immediate := SourceCurrentAllocatedLocalWorker.reduce_unchanged 0 0 0 0 0 0 0 0 0 budget loaded inherited
    values before fourth memo branch
  obtain ⟨rfl, rfl, _sameFourth, rfl⟩ := SourceCurrentAllocatedLocalWorkerStability.reduce_done_unique done immediate
  exact ⟨next, final, requests, actual, reads, receipt, SourceCurrentAllocatedLocalWorkerCompletion.reduce_complete actual,
    finalNative, finalOutput, finalProfiles, trace,
    Nat.eq_zero_of_le_zero (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.nodeBudget, branch] using nodes),
    Nat.eq_zero_of_le_zero (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.edgeBudget, branch] using edges)⟩

theorem constructed_emptyChildren (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (heightBound : childrenHeight values ≤ bound)
    (branch : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .emptyChildren)
    (capacity : Capacity bits before) :
    ∃ next final requests,
    ∃ actual : Reduction budget loaded inherited values before fourth memo (EqualityLeafProjectionRuntimeEmpty.erase values)
        (prefixState before loaded inherited) fourth memo,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next original loaded inherited values (EqualityLeafProjectionRuntimeEmpty.erase values) before
        (prefixState before loaded inherited) fourth fourth memo memo final ∧
      SourceCurrentAllocatedLocalWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n
          budget loaded inherited values before fourth memo) (EqualityLeafProjectionRuntimeEmpty.erase values) (prefixState before loaded inherited) fourth memo ∧
      NativeStored (prefixState before loaded inherited).native ∧
      OutputStored (prefixState before loaded inherited).native ∧ Profiles memo ∧
      Trace before.native.machine.heap (prefixState before loaded inherited).native.machine.heap requests ∧
      nodeRequests requests = 0 ∧ edgeRequests requests = 0 := by
  have pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth := by
    intro records actual
    rw [branch] at actual
    cases actual
  obtain ⟨results, after, saved, next, final, requests, actual, reads, receipt, stable,
    finalNative, finalOutput, finalProfiles, _produced, _related, _length, _height, trace, nodes, edges,
    _capacity, _nodeSupply, _edgeSupply⟩ := SourceCurrentAllocatedFiniteOrdinaryLocalResources.complete formulas solver
      inventory bits budget original loaded inherited values before fourth memo ready admitted cached found inheritedReady
      available correct physical profiles native output covered memos valid rows arity count depth bound profile lengthBound
      pathsBound heightBound
      (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.nodeBudget, branch, Nat.add_zero] using capacity.1)
      (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.edgeBudget, branch, Nat.add_zero] using capacity.2)
  obtain ⟨g, s, r, e, p, h, m, c, n, enough⟩ := stable
  have done := enough g s r e p h m c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have immediate := SourceCurrentAllocatedLocalWorker.reduce_emptyChildren 0 0 0 0 0 0 0 0 0 budget loaded inherited
    values before fourth memo branch
  obtain ⟨rfl, rfl, _sameFourth, rfl⟩ := SourceCurrentAllocatedLocalWorkerStability.reduce_done_unique done immediate
  exact ⟨next, final, requests, actual, reads, receipt, SourceCurrentAllocatedLocalWorkerCompletion.reduce_complete actual,
    finalNative, finalOutput, finalProfiles, trace,
    Nat.eq_zero_of_le_zero (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.nodeBudget, branch] using nodes),
    Nat.eq_zero_of_le_zero (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.edgeBudget, branch] using edges)⟩

end MicroCFTA.LocalParentResourceChecks

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms MicroCFTA.LocalParentResourceChecks.constructed_unchanged
#check @MicroCFTA.LocalParentResourceChecks.constructed_unchanged
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms MicroCFTA.LocalParentResourceChecks.constructed_emptyChildren
#check @MicroCFTA.LocalParentResourceChecks.constructed_emptyChildren


/-!
# Parent resources with the full returned outer caller

The initial loaded field selects the numeric budget.
The constructed parent graph supplies the same caller body and strict Reads.
Its receipt retains outer cells, probes, global memos, and the language law.
No future range or capacity plan is an input.
-/
namespace MicroCFTA.ParentCallerResourceChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialState (EdgeRequest advance)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialGraph (EdgeBody)
open SourceCurrentAllocatedPartialSourceReads (EdgeBodyReads)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
open SourceCurrentAllocatedFiniteOrdinaryParentResources (nodeBudget edgeBudget outputRows outputArity)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

theorem constructed_caller_then_scan (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {inventory : Inventory}
    (bits budget : Nat) (request : EdgeRequest) (loaded : Allocated) {before : Caller (bits + 2)}
    {memos : EndpointMemoGateTrace.Memos} (initial : Context formulas solver inventory before memos)
    (found : SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints = .ok (some loaded))
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value)
    (profiles : Profiles before.merge) (native : NativeStored before.checked.native) (output : OutputStored before.checked.native)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity request.value.children)
    (lengthBound : request.value.children.length ≤ count)
    (pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard request.inherited before.checked.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight request.value.children ≤ bound)
    (nodes : before.checked.native.machine.heap.nodes.next + nodeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + edgeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ≤ 2 ^ (bits + 2))
    (followup : EqualityNormalize.Constraints) :
    ∃ result checked saved next final requests,
    ∃ actual : EdgeBody budget request before result (advance before checked before.fourth saved),
      EdgeBodyReads formulas solver actual memos final ∧
      SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result (advance before checked before.fourth saved) final ∧
      Post formulas solver next before (advance before checked before.fourth saved) final ∧
      SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
          request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
          before.checked before.fourth before.merge) result checked before.fourth saved ∧
      NativeStored checked.native ∧ OutputStored checked.native ∧ Profiles saved ∧
      EdgeShape (outputRows request.value.entry.key.constraint loaded request.inherited before.checked.operations rows count depth bound)
        (outputArity request.value.entry.key.constraint loaded request.inherited before.checked.operations arity count) result ∧
      EdgeNarrow request.value result ∧ Trace before.checked.native.machine.heap checked.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ∧
      edgeRequests requests ≤ edgeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ∧
      Capacity bits checked ∧
      checked.native.machine.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next + nodeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ∧
      checked.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next + edgeBudget request.value.entry.key.constraint loaded request.inherited before.checked.operations rows arity count depth bound ∧
      ∃ scan : SourceCurrentConjunctionClassScan.Scan budget SourceMemoGate.unconstrained
        (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) result.children followup checked before.fourth
          none followup checked before.fourth,
        SourceCurrentAllocatedScanSourceReads.ScanReads scan final final := by
  obtain ⟨result, checked, saved, next, final, requests, actual, reads, receipt, post, stable, finalNative,
    finalOutput, finalProfiles, produced, narrowed, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryParentCallerResources.complete formulas solver bits budget request loaded initial
      found inherited resident profiles native output rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  have available := post.context.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ result receipt.resident
  obtain ⟨scan, scanReads⟩ := SourceCurrentAllocatedFiniteOrdinaryScan.construct budget result.children followup checked
    before.fourth post.context.ready available (EdgeShape.domain result produced) final
  exact ⟨result, checked, saved, next, final, requests, actual, reads, receipt, post, stable, finalNative, finalOutput,
    finalProfiles, produced, narrowed, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply, scan, scanReads⟩

end MicroCFTA.ParentCallerResourceChecks

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms MicroCFTA.ParentCallerResourceChecks.constructed_caller_then_scan
#check @MicroCFTA.ParentCallerResourceChecks.constructed_caller_then_scan
