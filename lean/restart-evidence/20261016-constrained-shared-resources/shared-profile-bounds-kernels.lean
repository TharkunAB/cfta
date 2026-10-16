import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedProfileBounds

namespace MicroCFTA.SharedProfileBoundChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityClassOrder (Record Coherent)
open SourceEqualityClassTarget (operandPaths)
open SourceCurrentAllocatedFiniteOrdinarySharedProfileBounds
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open MergedOrdinaryHeight (height childrenHeight)

/-- Exclusion retains the original order and makes two operands from three distinct paths. -/
theorem three_member_order :
    operandPaths [[0], [1], [2]] [1] = [[0], [2]] ∧
    (operandPaths [[0], [1], [2]] [1]).length = 2 ∧
    (∀ path ∈ operandPaths [[0], [1], [2]] [1], path.length ≤ 1) := by decide

/-- A singleton class has an empty target, with zero rows and both zero request budgets. -/
theorem singleton_target (rows arity count depth bound : Nat) (path : EqualityNormalize.Path) :
    Target.outputRows rows count depth bound (operandPaths [path] path).length = 0 ∧
    Target.nodeBudget rows arity count depth bound (operandPaths [path] path).length = 0 ∧
    Target.edgeBudget rows arity count depth bound (operandPaths [path] path).length = 0 := by
  simp [operandPaths, EqualityNarrowing.others, Target.outputRows, Target.nodeBudget, Target.edgeBudget]

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "N" => Target.nodeBudget
local notation "E" => Target.edgeBudget
local notation "StableRun" => SourceCurrentAllocatedTargetWorkerCompletion.StableRun
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- One original record bound constructs the selected Target and bounds its same actual returned state. -/
theorem original_record_target
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : Record) (coherent : Coherent record) (selected : EqualityNormalize.Path)
    (member : selected ∈ record.paths) (bits : Nat) (values : List (Value Symbol Guard))
    (before : Checked (bits + 2)) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (profiles : Profiles memo) (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound members : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (recordLength : record.paths.length ≤ members)
    (recordDepth : ∀ path ∈ record.paths, path.length ≤ depth) (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + N rows arity count depth bound (members - 1) ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + E rows arity count depth bound (members - 1) ≤ 2 ^ (bits + 2)) :
    ∃ result after saved next final,
      ∃ actual : Target values (operandPaths record.paths selected) before memo result after saved,
        StableRun (fun p h m s n => SourceCurrentAllocatedTargetWorker.target p h m s n values
          (operandPaths record.paths selected) before memo) result after saved ∧
        TargetReads formulas solver actual memos final ∧
        Receipt formulas solver next values (operandPaths record.paths selected) before memo result after saved memos final ∧
        NodeShape (Target.outputRows rows count depth bound (members - 1)) (max arity 1) result ∧
        height result ≤ bound ∧ Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧
        after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + N rows arity count depth bound (members - 1) ∧
        after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + E rows arity count depth bound (members - 1) := by
  obtain ⟨_rowsBound, nodeBound, edgeBound, pathsBound⟩ :=
    record_target_bounds record coherent selected member rows arity count depth bound members recordLength recordDepth
  obtain ⟨result, after, saved, next, final, _requests, actual, stable, reads, receipt,
    savedProfiles, afterNative, afterOutput, resultProfile, resultHeight, _trace,
    _nodeCount, _edgeCount, _capacity, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryTargetResources.target_complete formulas solver inventory bits values
      (operandPaths record.paths selected) before memo ready admitted available physical profiles native output
      covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound
      (by omega) (by omega)
  exact ⟨result, after, saved, next, final, actual, stable, reads, receipt,
    record_profile record coherent selected member rows (max arity 1) count depth bound members recordLength result resultProfile,
    resultHeight, savedProfiles, afterNative, afterOutput, by omega, by omega⟩

#print axioms three_member_order
#check @three_member_order
#print axioms singleton_target
#check @singleton_target
#print axioms original_record_target
#check @original_record_target
end MicroCFTA.SharedProfileBoundChecks
