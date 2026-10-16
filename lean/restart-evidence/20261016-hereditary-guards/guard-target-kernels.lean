import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardTarget
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetResources

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 2000000
set_option format.width 200

namespace GuardTargetResourceKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "NodeBudget" => SourceCurrentAllocatedFiniteOrdinaryTargetResources.nodeBudget
local notation "EdgeBudget" => SourceCurrentAllocatedFiniteOrdinaryTargetResources.edgeBudget
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial headroom constructs the exact Target before its same reads derive hereditary guards. -/
theorem constructed_target
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (bits : Nat) (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked (bits + 2)) (memo : Memo) (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (profiles : SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored memo)
    (native : SourceCurrentAllocatedFiniteOrdinaryStored.Stored before.native)
    (output : SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored before.native)
    (mergedGuards : SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored memo)
    (nativeGuards : SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : EndpointMemoGateTrace.Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + NodeBudget rows arity count depth bound paths.length ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + EdgeBudget rows arity count depth bound paths.length ≤ 2 ^ (bits + 2)) :
    ∃ result after saved next final requests,
      ∃ actual : SourceCurrentAllocatedTargetGraph.Target values paths before memo result after saved,
        SourceCurrentAllocatedTargetWorkerCompletion.StableRun
          (fun p h m s n => SourceCurrentAllocatedTargetWorker.target p h m s n values paths before memo) result after saved ∧
        SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final ∧
        SourceCurrentAllocatedTargetComplete.Receipt formulas solver next values paths before memo result after saved memos final ∧
        SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored saved ∧
        SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored after.native ∧
        SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
          (SourceCurrentAllocatedFiniteOrdinaryGuardTarget.targetLimit
            (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.childrenLimits values) paths) result ∧
        SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace.Trace
          before.native.machine.heap after.native.machine.heap requests ∧
        SourceCurrentAllocatedFiniteOrdinaryReservations.nodeRequests requests ≤ NodeBudget rows arity count depth bound paths.length ∧
        SourceCurrentAllocatedFiniteOrdinaryReservations.edgeRequests requests ≤ EdgeBudget rows arity count depth bound paths.length ∧
        SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after := by
  obtain ⟨result, after, saved, next, final, requests, actual, stable, reads, receipt, _oldMerge, _oldNative,
    _oldOutput, _shape, _height, trace, nodeCount, edgeCount, capacity, _nodeSupply, _edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryTargetResources.target_complete formulas solver inventory bits values paths
      before memo ready admitted available physical profiles native output covered memos valid
      rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  have guardProfile := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.children_self values
    (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.ChildrenShape.domain values profile)
  have produced := SourceCurrentAllocatedFiniteOrdinaryGuardTarget.target_reads reads ready available physical
    mergedGuards nativeGuards _ guardProfile
  exact ⟨result, after, saved, next, final, requests, actual, stable, reads, receipt,
    produced.1, produced.2.1, produced.2.2, trace, nodeCount, edgeCount, capacity⟩

end GuardTargetResourceKernels
#print axioms GuardTargetResourceKernels.constructed_target
#check @GuardTargetResourceKernels.constructed_target
